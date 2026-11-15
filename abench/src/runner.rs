// SPDX-License-Identifier: MIT

//! Benchmark registry, warm-up, batched `KeepRunning` state machine, and mode runners.

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write;
use core::hint::black_box;

use crate::counter::{counter_delta, CounterSource, Snapshot, PMU_COUNT, PMU_SUFFIXES, PMU_UNITS};
use crate::results::{ResultsSet, JSON_BEGIN_MARKER, JSON_END_MARKER, TEST_SUITE};

/// Number of timed runs executed per benchmark in unit-test check mode (`perftest` default).
pub const UNIT_TEST_BATCHES: u32 = 3;

/// Number of warm-up iterations executed before unit-test runs.
pub const UNIT_TEST_WARMUP: u32 = 1;

/// Configuration for running registered benchmarks in perf-test mode.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PerfConfig {
    pub test_suite: String,
    pub batches: u32,
    pub iterations_per_batch: u32,
    pub warmup_iterations: u32,
    pub filter: Option<String>,
    pub random_seed: Option<u64>,
    pub quiet: bool,
}

impl Default for PerfConfig {
    fn default() -> Self {
        Self {
            test_suite: String::from(TEST_SUITE),
            batches: 20,
            iterations_per_batch: 16,
            warmup_iterations: 4,
            filter: None,
            random_seed: None,
            quiet: false,
        }
    }
}

/// Report returned by [`Registry::run_unit_test`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnitTestReport {
    pub total: usize,
    pub passed: usize,
    pub failed: usize,
}

/// Per-benchmark execution state passed into closure-based tests (`while state.keep_running()`).
pub struct RepeatState<'a> {
    counters: &'a mut dyn CounterSource,
    warmup_remaining: u32,
    batches: u32,
    iterations_per_batch: u32,
    step_names: Vec<String>,
    step_count: u32,
    started: bool,
    finished: bool,
    in_warmup: bool,
    error: Option<&'static str>,
    step_in_iter: u32,
    current_batch: u32,
    iter_in_batch: u32,
    snapshots: Vec<Snapshot>,
    next_snapshot_idx: usize,
}

impl<'a> RepeatState<'a> {
    fn new(
        counters: &'a mut dyn CounterSource,
        warmup_iterations: u32,
        batches: u32,
        iterations_per_batch: u32,
    ) -> Self {
        Self {
            counters,
            warmup_remaining: warmup_iterations,
            batches,
            iterations_per_batch,
            step_names: Vec::new(),
            step_count: 0,
            started: false,
            finished: false,
            in_warmup: false,
            error: None,
            step_in_iter: 0,
            current_batch: 0,
            iter_in_batch: 0,
            snapshots: Vec::new(),
            next_snapshot_idx: 0,
        }
    }

    fn set_error(&mut self, msg: &'static str) {
        if self.error.is_none() {
            self.error = Some(msg);
        }
    }

    /// Declares an ordered step within each iteration before calling [`Self::keep_running`].
    /// Steps ending in `_ignore` are timed and verified for call counts but omitted from output.
    pub fn declare_step(&mut self, name: &str) {
        if self.started {
            self.set_error("declare_step called after keep_running");
            return;
        }
        if name.is_empty() {
            self.set_error("Empty step name");
            return;
        }
        if self.step_names.iter().any(|existing| existing == name) {
            self.set_error("Found duplicate step name in multi-step test");
            return;
        }
        self.step_names.push(String::from(name));
    }

    /// Marks the boundary between two consecutive declared steps within one iteration.
    #[inline]
    pub fn next_step(&mut self) {
        if !self.started || self.finished || self.error.is_some() {
            self.set_error("next_step called outside an active iteration");
            return;
        }
        if self.step_in_iter + 1 >= self.step_count {
            self.set_error("Too many calls to next_step");
            return;
        }
        self.step_in_iter += 1;
        if !self.in_warmup {
            self.snapshots[self.next_snapshot_idx] = self.counters.snapshot();
            self.next_snapshot_idx += 1;
        }
    }

    /// Advances warm-up or timed batch state; returns `false` once all iterations complete or on error.
    #[inline]
    pub fn keep_running(&mut self) -> bool {
        if !self.started {
            return self.begin();
        }
        if self.finished {
            self.set_error("Too many calls to keep_running");
            return false;
        }
        if self.step_in_iter != self.step_count - 1 {
            self.set_error("Wrong number of calls to next_step");
            self.finished = true;
            return false;
        }
        self.step_in_iter = 0;
        if self.in_warmup {
            if self.warmup_remaining > 0 {
                self.warmup_remaining -= 1;
                return true;
            }
            self.in_warmup = false;
            self.current_batch = 0;
            self.iter_in_batch = 0;
            self.snapshots[0] = self.counters.snapshot();
            self.next_snapshot_idx = 1;
            return true;
        }

        self.iter_in_batch += 1;
        if self.step_count == 1 {
            if self.iter_in_batch == self.iterations_per_batch {
                self.snapshots[self.next_snapshot_idx] = self.counters.snapshot();
                self.next_snapshot_idx += 1;
                self.current_batch += 1;
                self.iter_in_batch = 0;
                if self.current_batch == self.batches {
                    self.finished = true;
                    return false;
                }
            }
            return true;
        }

        self.snapshots[self.next_snapshot_idx] = self.counters.snapshot();
        self.next_snapshot_idx += 1;
        if self.iter_in_batch == self.iterations_per_batch {
            self.current_batch += 1;
            self.iter_in_batch = 0;
            if self.current_batch == self.batches {
                self.finished = true;
                return false;
            }
        }
        true
    }

    fn begin(&mut self) -> bool {
        if self.error.is_some() {
            return false;
        }
        self.started = true;
        self.step_count = if self.step_names.is_empty() {
            1
        } else {
            self.step_names.len() as u32
        };
        if self.batches == 0 || self.iterations_per_batch == 0 {
            self.finished = true;
            return false;
        }
        let slots = if self.step_count == 1 {
            (self.batches as usize) + 1
        } else {
            (self.batches as usize) * (self.iterations_per_batch as usize) * (self.step_count as usize)
                + 1
        };
        self.snapshots = alloc::vec![Snapshot::default(); slots];
        // Barrier the zero-initialized allocation so backing pages fault cleanly before batch 0.
        black_box(self.snapshots.as_ptr());
        self.step_in_iter = 0;
        if self.warmup_remaining > 0 {
            self.in_warmup = true;
            self.warmup_remaining -= 1;
            return true;
        }
        self.in_warmup = false;
        self.current_batch = 0;
        self.iter_in_batch = 0;
        self.snapshots[0] = self.counters.snapshot();
        self.next_snapshot_idx = 1;
        true
    }

    fn finish_check(&self, returned_ok: bool) -> Result<(), &'static str> {
        if let Some(err) = self.error {
            return Err(err);
        }
        if !self.finished {
            return Err("Too few calls to keep_running");
        }
        if !returned_ok {
            return Err("Test function returned false");
        }
        Ok(())
    }

    fn append_results(&self, test_suite: &str, test_name: &str, dest: &mut ResultsSet) {
        if self.batches == 0 || self.iterations_per_batch == 0 {
            return;
        }
        let tsc_hz = self.counters.ticks_per_second();
        if self.step_count == 1 {
            if self.step_names.first().is_some_and(|n| n.ends_with("_ignore")) {
                return;
            }
            self.emit_single_step_series(test_suite, test_name, tsc_hz, dest);
        } else {
            for step in 0..(self.step_count as usize) {
                let step_name = &self.step_names[step];
                if step_name.ends_with("_ignore") {
                    continue;
                }
                let label = format!("{test_name}.{step_name}");
                self.emit_multi_step_series(test_suite, &label, step, tsc_hz, dest);
            }
        }
    }

    fn emit_single_step_series(
        &self,
        test_suite: &str,
        label: &str,
        tsc_hz: Option<u64>,
        dest: &mut ResultsSet,
    ) {
        let batches = self.batches as usize;
        let inv_iters = 1.0 / (self.iterations_per_batch as f64);
        if let Some(hz) = tsc_hz {
            let ns_per_tick = 1_000_000_000.0 / (hz as f64);
            let ns = dest.add_test_case(test_suite, label, "nanoseconds");
            ns.values.reserve(batches);
            for b in 0..batches {
                let ticks = counter_delta(self.snapshots[b].tsc, self.snapshots[b + 1].tsc);
                ns.values.push((ticks as f64) * inv_iters * ns_per_tick);
            }
        }
        let tsc_label = format!("{label}.tsc_cycles");
        let tsc = dest.add_test_case(test_suite, &tsc_label, "cycles");
        tsc.values.reserve(batches);
        for b in 0..batches {
            let ticks = counter_delta(self.snapshots[b].tsc, self.snapshots[b + 1].tsc);
            tsc.values.push((ticks as f64) * inv_iters);
        }
        let has_pmu = (0..batches)
            .all(|b| self.snapshots[b].pmu.is_some() && self.snapshots[b + 1].pmu.is_some());
        if has_pmu {
            for idx in 0..PMU_COUNT {
                let pmu_label = format!("{label}.{}", PMU_SUFFIXES[idx]);
                let entry = dest.add_test_case(test_suite, &pmu_label, PMU_UNITS[idx]);
                entry.values.reserve(batches);
                for b in 0..batches {
                    let start = self.snapshots[b].pmu.expect("checked")[idx];
                    let end = self.snapshots[b + 1].pmu.expect("checked")[idx];
                    entry
                        .values
                        .push((counter_delta(start, end) as f64) * inv_iters);
                }
            }
        }
    }

    fn emit_multi_step_series(
        &self,
        test_suite: &str,
        label: &str,
        step: usize,
        tsc_hz: Option<u64>,
        dest: &mut ResultsSet,
    ) {
        let batches = self.batches as usize;
        let iters = self.iterations_per_batch as usize;
        let steps = self.step_count as usize;
        let inv_iters = 1.0 / (iters as f64);
        let mut batch_ticks = Vec::with_capacity(batches);
        let mut batch_pmu = [Vec::new(), Vec::new(), Vec::new(), Vec::new()];
        let has_pmu = self.snapshots.iter().all(|s| s.pmu.is_some());
        if has_pmu {
            for vec in &mut batch_pmu {
                vec.reserve(batches);
            }
        }

        for b in 0..batches {
            let mut sum_tsc: u128 = 0;
            let mut sum_pmu: [u128; PMU_COUNT] = [0; PMU_COUNT];
            for k in 0..iters {
                let idx = (b * iters + k) * steps + step;
                let a = &self.snapshots[idx];
                let z = &self.snapshots[idx + 1];
                sum_tsc += counter_delta(a.tsc, z.tsc) as u128;
                if has_pmu {
                    let pa = a.pmu.expect("checked");
                    let pz = z.pmu.expect("checked");
                    for c in 0..PMU_COUNT {
                        sum_pmu[c] += counter_delta(pa[c], pz[c]) as u128;
                    }
                }
            }
            batch_ticks.push((sum_tsc as f64) * inv_iters);
            if has_pmu {
                for c in 0..PMU_COUNT {
                    batch_pmu[c].push((sum_pmu[c] as f64) * inv_iters);
                }
            }
        }

        if let Some(hz) = tsc_hz {
            let ns_per_tick = 1_000_000_000.0 / (hz as f64);
            let ns = dest.add_test_case(test_suite, label, "nanoseconds");
            ns.values = batch_ticks.iter().map(|&v| v * ns_per_tick).collect();
        }
        let tsc_label = format!("{label}.tsc_cycles");
        dest.add_test_case(test_suite, &tsc_label, "cycles").values = batch_ticks;
        if has_pmu {
            for (c, values) in batch_pmu.into_iter().enumerate() {
                let pmu_label = format!("{label}.{}", PMU_SUFFIXES[c]);
                dest.add_test_case(test_suite, &pmu_label, PMU_UNITS[c])
                    .values = values;
            }
        }
    }
}

type TestFn = Box<dyn FnMut(&mut RepeatState<'_>) -> bool>;

/// Named registry of benchmarks executed in deterministic sorted or seeded-random order.
#[derive(Default)]
pub struct Registry {
    tests: Vec<(String, TestFn)>,
}

impl Registry {
    /// Creates an empty benchmark registry.
    pub const fn new() -> Self {
        Self { tests: Vec::new() }
    }

    /// Registers a multi-step or fixture-bearing benchmark under `name`.
    pub fn register<F>(&mut self, name: impl Into<String>, func: F) -> Result<(), &'static str>
    where
        F: FnMut(&mut RepeatState<'_>) -> bool + 'static,
    {
        let name = name.into();
        if name.is_empty() {
            return Err("Benchmark name must not be empty");
        }
        if self.tests.iter().any(|(existing, _)| existing == &name) {
            return Err("Duplicate benchmark name");
        }
        self.tests.push((name, Box::new(func)));
        Ok(())
    }

    /// Registers a single-step benchmark closure whose body runs once per iteration.
    pub fn register_simple<F>(
        &mut self,
        name: impl Into<String>,
        mut func: F,
    ) -> Result<(), &'static str>
    where
        F: FnMut() -> bool + 'static,
    {
        self.register(name, move |state| {
            while state.keep_running() {
                if !func() {
                    return false;
                }
            }
            true
        })
    }

    /// Returns the number of registered benchmarks.
    pub fn len(&self) -> usize {
        self.tests.len()
    }

    /// Returns whether no benchmarks are registered.
    pub fn is_empty(&self) -> bool {
        self.tests.is_empty()
    }

    /// Executes matching benchmarks in unit-test check mode (`UNIT_TEST_BATCHES` runs, no JSON/timings).
    pub fn run_unit_test(
        &mut self,
        out: &mut dyn Write,
        filter: Option<&str>,
    ) -> Result<UnitTestReport, &'static str> {
        let indices = select_indices(&self.tests, filter, None)?;
        let mut noop_counters = UnitTestCounters;
        let _ = writeln!(out, "Running perf tests in unit test mode...");
        let mut passed = 0usize;
        let mut failed = 0usize;
        for idx in indices {
            let (ref name, ref mut func) = self.tests[idx];
            let _ = writeln!(out, "[ RUN      ] {name}");
            let mut state = RepeatState::new(&mut noop_counters, UNIT_TEST_WARMUP, UNIT_TEST_BATCHES, 1);
            let ok = func(&mut state);
            match state.finish_check(ok) {
                Ok(()) => {
                    passed += 1;
                    let _ = writeln!(out, "[       OK ] {name}");
                }
                Err(reason) => {
                    failed += 1;
                    let _ = writeln!(out, "Error: {reason}");
                    let _ = writeln!(out, "[  FAILED  ] {name}");
                }
            }
        }
        let total = passed + failed;
        let _ = writeln!(out, "abench unit-test: {passed} passed, {failed} failed");
        Ok(UnitTestReport {
            total,
            passed,
            failed,
        })
    }

    /// Executes matching benchmarks in perf-test mode, prints summary + JSON, and returns results.
    pub fn run_perf_test(
        &mut self,
        config: &PerfConfig,
        counters: &mut dyn CounterSource,
        out: &mut dyn Write,
    ) -> Result<ResultsSet, &'static str> {
        if config.batches == 0 || config.iterations_per_batch == 0 {
            return Err("PerfConfig batches and iterations_per_batch must be non-zero");
        }
        let indices = select_indices(&self.tests, config.filter.as_deref(), config.random_seed)?;
        let mut results = ResultsSet::new();
        for idx in indices {
            let (ref name, ref mut func) = self.tests[idx];
            if !config.quiet {
                let _ = writeln!(out, "[ RUN      ] {name}");
            }
            let mut state = RepeatState::new(
                counters,
                config.warmup_iterations,
                config.batches,
                config.iterations_per_batch,
            );
            let ok = func(&mut state);
            if let Err(reason) = state.finish_check(ok) {
                let _ = writeln!(out, "Error: {reason}");
                let _ = writeln!(out, "[  FAILED  ] {name}");
                return Err(reason);
            }
            state.append_results(&config.test_suite, name, &mut results);
            if !config.quiet {
                let _ = writeln!(out, "[       OK ] {name}");
            }
        }
        if !config.quiet {
            let _ = out.write_char('\n');
            let _ = results.print_summary_table(out);
            let _ = out.write_char('\n');
        }
        let _ = writeln!(out, "{JSON_BEGIN_MARKER}");
        let _ = results.write_json(out);
        let _ = out.write_char('\n');
        let _ = writeln!(out, "{JSON_END_MARKER}");
        Ok(results)
    }
}

struct UnitTestCounters;

impl CounterSource for UnitTestCounters {
    fn snapshot(&mut self) -> Snapshot {
        Snapshot::default()
    }

    fn ticks_per_second(&self) -> Option<u64> {
        None
    }
}

fn select_indices(
    tests: &[(String, TestFn)],
    filter: Option<&str>,
    random_seed: Option<u64>,
) -> Result<Vec<usize>, &'static str> {
    if tests.is_empty() {
        return Err("No test cases are registered");
    }
    let mut indices: Vec<usize> = tests
        .iter()
        .enumerate()
        .filter(|(_, (name, _))| filter.is_none_or(|pat| matches_glob(pat, name)))
        .map(|(i, _)| i)
        .collect();
    if indices.is_empty() {
        return Err("Filter did not match any benchmark");
    }
    if let Some(seed) = random_seed {
        // Fisher-Yates shuffle driven by SplitMix64 for reproducible randomized ordering.
        indices.sort_by(|&a, &b| tests[a].0.cmp(&tests[b].0));
        let mut s = seed ^ 0x9e37_79b9_7f4a_7c15;
        for i in (1..indices.len()).rev() {
            s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^= z >> 31;
            let j = (z as usize) % (i + 1);
            indices.swap(i, j);
        }
    } else {
        indices.sort_by(|&a, &b| tests[a].0.cmp(&tests[b].0));
    }
    Ok(indices)
}

fn matches_glob(pattern: &str, text: &str) -> bool {
    if pattern.is_empty() {
        return true;
    }
    if !pattern.contains('*') {
        return text.contains(pattern);
    }
    let parts: Vec<&str> = pattern.split('*').collect();
    let mut rest = text;
    let first = parts[0];
    if !first.is_empty() {
        let Some(stripped) = rest.strip_prefix(first) else {
            return false;
        };
        rest = stripped;
    }
    let last = *parts.last().unwrap_or(&"");
    for &middle in &parts[1..parts.len().saturating_sub(1)] {
        if middle.is_empty() {
            continue;
        }
        let Some(pos) = rest.find(middle) else {
            return false;
        };
        rest = &rest[pos + middle.len()..];
    }
    if last.is_empty() {
        true
    } else {
        rest.ends_with(last)
    }
}

/// Registers the built-in self-calibration cases (`Null`, `Null5Step`, `NoOpLoop/{100,1000,10000}`).
pub fn register_calibration_benchmarks(registry: &mut Registry) -> Result<(), &'static str> {
    registry.register_simple("Null", || true)?;
    registry.register("Null5Step", |state| {
        state.declare_step("step1");
        state.declare_step("step2");
        state.declare_step("step3");
        state.declare_step("step4");
        state.declare_step("step5");
        while state.keep_running() {
            state.next_step();
            state.next_step();
            state.next_step();
            state.next_step();
        }
        true
    })?;
    for &count in &[100usize, 1_000, 10_000] {
        registry.register_simple(format!("NoOpLoop/{count}"), move || {
            for i in 0..count {
                black_box(i);
            }
            true
        })?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::counter::{Snapshot, PMU_COUNT};
    use crate::results::{extract_perftest_json, parse_perftest_json};
    use alloc::rc::Rc;
    use alloc::vec;
    use core::cell::{Cell, RefCell};

    struct FakeCounters {
        ticks: u64,
        pmu: Option<[u64; PMU_COUNT]>,
        step_ticks: u64,
        step_pmu: [u64; PMU_COUNT],
        tsc_hz: Option<u64>,
        snapshot_calls: usize,
    }

    impl FakeCounters {
        fn new(tsc_hz: Option<u64>, pmu: Option<[u64; PMU_COUNT]>) -> Self {
            Self {
                ticks: 1_000,
                pmu,
                step_ticks: 50,
                step_pmu: [100, 25, 4, 1],
                tsc_hz,
                snapshot_calls: 0,
            }
        }

        fn advance(&mut self, factor: u64) {
            self.ticks = self.ticks.wrapping_add(self.step_ticks * factor);
            if let Some(ref mut p) = self.pmu {
                for (slot, delta) in p.iter_mut().zip(self.step_pmu) {
                    *slot = slot.wrapping_add(delta * factor);
                }
            }
        }
    }

    impl CounterSource for FakeCounters {
        fn snapshot(&mut self) -> Snapshot {
            self.snapshot_calls += 1;
            Snapshot {
                tsc: self.ticks,
                pmu: self.pmu,
            }
        }

        fn ticks_per_second(&self) -> Option<u64> {
            self.tsc_hz
        }
    }

    #[derive(Clone)]
    struct SharedCounters(Rc<RefCell<FakeCounters>>);

    impl CounterSource for SharedCounters {
        fn snapshot(&mut self) -> Snapshot {
            self.0.borrow_mut().snapshot()
        }

        fn ticks_per_second(&self) -> Option<u64> {
            self.0.borrow().ticks_per_second()
        }
    }

    struct IoLog {
        text: String,
        inside_timed_hook: Rc<Cell<bool>>,
        saw_io_during_timed: bool,
    }

    impl IoLog {
        fn new(flag: Rc<Cell<bool>>) -> Self {
            Self {
                text: String::new(),
                inside_timed_hook: flag,
                saw_io_during_timed: false,
            }
        }
    }

    impl Write for IoLog {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            if self.inside_timed_hook.get() {
                self.saw_io_during_timed = true;
            }
            self.text.push_str(s);
            Ok(())
        }
    }

    #[test]
    fn registry_rejects_duplicates_and_empty_names_and_sorts_deterministically() {
        let mut reg = Registry::new();
        assert!(reg.register_simple("", || true).is_err());
        reg.register_simple("Syscall/Null", || true).unwrap();
        reg.register_simple("Null", || true).unwrap();
        assert!(reg.register_simple("Null", || true).is_err());

        let mut counters = FakeCounters::new(None, None);
        let mut out = String::new();
        let cfg = PerfConfig {
            batches: 2,
            iterations_per_batch: 1,
            warmup_iterations: 0,
            ..PerfConfig::default()
        };
        let results = reg.run_perf_test(&cfg, &mut counters, &mut out).unwrap();
        assert_eq!(results.results[0].label, "Null.tsc_cycles");
        assert_eq!(results.results[1].label, "Syscall/Null.tsc_cycles");
    }

    #[test]
    fn warmup_excluded_and_single_step_batching_amortizes_timer_reads() {
        let counters = Rc::new(RefCell::new(FakeCounters::new(
            Some(1_000_000_000),
            Some([u64::MAX - 50, 10, 20, 30]),
        )));
        let total_calls = Rc::new(Cell::new(0u32));
        let calls_ref = total_calls.clone();
        let c_ref = counters.clone();

        let mut reg = Registry::new();
        reg.register_simple("Syscall/Null", move || {
            let call = calls_ref.get();
            calls_ref.set(call + 1);
            // Make warm-up cycles obviously huge so if leaked into batch 0 the assertion catches it.
            let mult = if call < 3 { 10_000 } else { 1 };
            c_ref.borrow_mut().advance(mult);
            true
        })
        .unwrap();

        let cfg = PerfConfig {
            batches: 4,
            iterations_per_batch: 5,
            warmup_iterations: 3,
            ..PerfConfig::default()
        };
        let mut shared = SharedCounters(counters.clone());
        let mut out = String::new();
        let results = reg.run_perf_test(&cfg, &mut shared, &mut out).unwrap();

        assert_eq!(total_calls.get(), 3 + 4 * 5);
        // Single-step snapshots happen only at the (batches + 1) batch boundaries after warm-up.
        assert_eq!(counters.borrow().snapshot_calls, 5);

        let labels: Vec<&str> = results.results.iter().map(|r| r.label.as_str()).collect();
        assert_eq!(
            labels,
            vec![
                "Syscall/Null",
                "Syscall/Null.tsc_cycles",
                "Syscall/Null.cycles",
                "Syscall/Null.instructions",
                "Syscall/Null.fills",
                "Syscall/Null.ccx_fills",
            ]
        );
        // Per-iteration batch means match FakeCounters deltas cleanly even with u64 wraparound.
        assert_eq!(results.results[0].values, vec![50.0; 4]);
        assert_eq!(results.results[1].values, vec![50.0; 4]);
        assert_eq!(results.results[2].values, vec![100.0; 4]);
        assert_eq!(results.results[3].values, vec![25.0; 4]);
        assert_eq!(results.results[4].values, vec![4.0; 4]);
        assert_eq!(results.results[5].values, vec![1.0; 4]);

        let json_str = extract_perftest_json(&out).expect("JSON block present");
        let parsed = parse_perftest_json(json_str).expect("valid JSON");
        assert_eq!(parsed.len(), 6);
    }

    #[test]
    fn multistep_drops_ignore_steps_and_averages_batches() {
        let counters = Rc::new(RefCell::new(FakeCounters::new(None, None)));
        let c_ref = counters.clone();
        let mut reg = Registry::new();
        reg.register("Mutex/Pair", move |state| {
            state.declare_step("setup_ignore");
            state.declare_step("lock");
            state.declare_step("unlock");
            while state.keep_running() {
                c_ref.borrow_mut().advance(10); // setup_ignore: 500 ticks
                state.next_step();
                c_ref.borrow_mut().advance(2); // lock: 100 ticks
                state.next_step();
                c_ref.borrow_mut().advance(1); // unlock: 50 ticks
            }
            true
        })
        .unwrap();

        let cfg = PerfConfig {
            batches: 3,
            iterations_per_batch: 4,
            warmup_iterations: 2,
            ..PerfConfig::default()
        };
        let mut shared = SharedCounters(counters);
        let mut out = String::new();
        let results = reg.run_perf_test(&cfg, &mut shared, &mut out).unwrap();
        let labels: Vec<&str> = results.results.iter().map(|r| r.label.as_str()).collect();
        assert_eq!(
            labels,
            vec!["Mutex/Pair.lock.tsc_cycles", "Mutex/Pair.unlock.tsc_cycles"]
        );
        assert_eq!(results.results[0].values, vec![100.0; 3]);
        assert_eq!(results.results[1].values, vec![50.0; 3]);
    }

    #[test]
    fn no_io_occurs_during_timed_test_body() {
        let timed_flag = Rc::new(Cell::new(false));
        let flag_ref = timed_flag.clone();
        let mut reg = Registry::new();
        reg.register("Syscall/Null", move |state| {
            while state.keep_running() {
                flag_ref.set(true);
                core::hint::black_box(42);
            }
            flag_ref.set(false);
            true
        })
        .unwrap();

        let mut counters = FakeCounters::new(None, None);
        let mut io = IoLog::new(timed_flag);
        reg.run_perf_test(&PerfConfig::default(), &mut counters, &mut io)
            .unwrap();
        assert!(!io.saw_io_during_timed);
    }

    #[test]
    fn bad_keep_running_and_next_step_contracts_fail_cleanly() {
        for expected in 0..8 {
            let mut reg = Registry::new();
            reg.register("BadKeepRunning", move |state| {
                for _ in 0..expected {
                    let _ = state.keep_running();
                }
                true
            })
            .unwrap();
            let mut out = String::new();
            let report = reg.run_unit_test(&mut out, None).unwrap();
            if expected == (1 + UNIT_TEST_BATCHES + 1) as usize {
                assert_eq!(report.passed, 1, "exact iteration+stop count passes");
            } else {
                assert_eq!(report.failed, 1, "expected={expected} must fail");
            }
        }

        let mut dup_steps = Registry::new();
        dup_steps
            .register("DupSteps", |state| {
                state.declare_step("a");
                state.declare_step("a");
                while state.keep_running() {
                    state.next_step();
                }
                true
            })
            .unwrap();
        let mut out = String::new();
        assert_eq!(dup_steps.run_unit_test(&mut out, None).unwrap().failed, 1);

        let mut wrong_next = Registry::new();
        wrong_next
            .register("MissingNextStep", |state| {
                state.declare_step("a");
                state.declare_step("b");
                while state.keep_running() {}
                true
            })
            .unwrap();
        assert_eq!(wrong_next.run_unit_test(&mut out, None).unwrap().failed, 1);
    }

    #[test]
    fn calibration_benchmarks_run_in_both_unit_and_perf_modes() {
        let mut reg = Registry::new();
        register_calibration_benchmarks(&mut reg).unwrap();
        assert_eq!(reg.len(), 5);

        let mut out = String::new();
        let unit = reg.run_unit_test(&mut out, None).unwrap();
        assert_eq!(unit.passed, 5);
        assert_eq!(unit.failed, 0);
        assert!(extract_perftest_json(&out).is_none());

        let mut counters = FakeCounters::new(None, None);
        let mut perf_out = String::new();
        let cfg = PerfConfig {
            batches: 3,
            iterations_per_batch: 2,
            warmup_iterations: 1,
            ..PerfConfig::default()
        };
        let results = reg.run_perf_test(&cfg, &mut counters, &mut perf_out).unwrap();
        assert!(results.results.iter().any(|r| r.label == "Null.tsc_cycles"));
        assert!(results
            .results
            .iter()
            .any(|r| r.label == "Null5Step.step1.tsc_cycles"));
        assert!(results
            .results
            .iter()
            .any(|r| r.label == "NoOpLoop/1000.tsc_cycles"));
    }

    #[test]
    fn filter_and_random_order_behave_per_perftest_contract() {
        let mut reg = Registry::new();
        register_calibration_benchmarks(&mut reg).unwrap();
        reg.register_simple("Syscall/Null", || true).unwrap();

        let mut counters = FakeCounters::new(None, None);
        let mut out = String::new();
        let filtered = reg
            .run_perf_test(
                &PerfConfig {
                    batches: 2,
                    iterations_per_batch: 1,
                    warmup_iterations: 0,
                    filter: Some(String::from("Syscall/*")),
                    ..PerfConfig::default()
                },
                &mut counters,
                &mut out,
            )
            .unwrap();
        assert_eq!(filtered.results.len(), 1);
        assert_eq!(filtered.results[0].label, "Syscall/Null.tsc_cycles");

        let no_match = reg.run_perf_test(
            &PerfConfig {
                filter: Some(String::from("DoesNotExist/*")),
                ..PerfConfig::default()
            },
            &mut counters,
            &mut out,
        );
        assert!(no_match.is_err());

        let r1 = reg
            .run_perf_test(
                &PerfConfig {
                    batches: 1,
                    iterations_per_batch: 1,
                    warmup_iterations: 0,
                    random_seed: Some(12345),
                    ..PerfConfig::default()
                },
                &mut counters,
                &mut out,
            )
            .unwrap();
        assert_eq!(r1.results.len(), 10);
    }

    #[test]
    fn unit_test_reports_failure_when_benchmark_returns_false() {
        let mut reg = Registry::new();
        reg.register_simple("AlwaysPass", || true).unwrap();
        reg.register_simple("AlwaysFail", || false).unwrap();
        let mut out = String::new();
        let report = reg.run_unit_test(&mut out, None).unwrap();
        assert_eq!(report.total, 2);
        assert_eq!(report.passed, 1);
        assert_eq!(report.failed, 1);
        assert!(out.contains("[  FAILED  ] AlwaysFail"));
    }
}
