// SPDX-License-Identifier: MIT

//! The loader's own stack, filled with a pattern before `load` runs on it, so that `load` can say
//! how far down the stack it wrote before entering the kernel. design/test-guest-memory/.

use core::sync::atomic::{AtomicU64, Ordering};

/// What every word of the stack holds before `load` runs: "loadrstk".
const PAINT: u64 = 0x6b74_7372_6461_6f6c;

/// The stack's lowest address and its length in bytes, set once by `paint`.
static BASE: AtomicU64 = AtomicU64::new(0);
static SIZE: AtomicU64 = AtomicU64::new(0);

/// Fills the `size` bytes at `base` with the pattern and records them as the loader's stack.
///
/// # Safety
///
/// The bytes are the loader's, unused, 8-byte aligned and a multiple of 8 long, and nothing runs on
/// them yet.
pub unsafe fn paint(base: u64, size: u64) {
    fill(base, size);
    BASE.store(base, Ordering::SeqCst);
    SIZE.store(size, Ordering::SeqCst);
}

/// How many bytes of the stack `paint` recorded have been written, and the stack's length.
pub fn depth() -> (u64, u64) {
    let size = SIZE.load(Ordering::SeqCst);
    assert!(size != 0, "the loader's stack was painted");
    // `paint` filled these bytes and they stay the loader's.
    (unsafe { written(BASE.load(Ordering::SeqCst), size) }, size)
}

/// Fills the `size` bytes at `base` with the pattern.
///
/// # Safety
///
/// As for `paint`.
unsafe fn fill(base: u64, size: u64) {
    assert!(base % 8 == 0 && size % 8 == 0, "the loader's stack is in words");
    let words = base as *mut u64;
    for index in 0..(size / 8) as usize {
        words.add(index).write_volatile(PAINT);
    }
}

/// The bytes of the `size`-byte stack at `base` counted down from its top to the lowest word that
/// no longer holds the pattern. A word written with the pattern itself is not seen, so this is a
/// lower bound on what was written.
///
/// # Safety
///
/// The bytes are readable. They are read without a reference, since the stack the caller runs on
/// is among them.
unsafe fn written(base: u64, size: u64) -> u64 {
    let words = base as *const u64;
    let untouched = (0..(size / 8) as usize)
        .take_while(|&index| words.add(index).read_volatile() == PAINT)
        .count();
    size - untouched as u64 * 8
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The written bytes of a painted `words`-word stack whose top `top` words were written and,
    /// below the lowest of them, a word the pattern survives in, as a frame that skips a slot
    /// leaves one.
    fn written_after(words: usize, top: usize) -> u64 {
        let mut stack = vec![0u64; words];
        let (base, size) = (stack.as_mut_ptr() as u64, (words * 8) as u64);
        unsafe { fill(base, size) };
        for word in &mut stack[words - top..] {
            *word = 0;
        }
        if top > 2 {
            stack[words - top + 1] = PAINT;
        }
        unsafe { written(stack.as_ptr() as u64, size) }
    }

    #[test]
    fn a_stack_nothing_ran_on_has_nothing_written() {
        assert_eq!(written_after(64, 0), 0);
    }

    #[test]
    fn the_depth_is_from_the_top_to_the_lowest_word_written() {
        assert_eq!(written_after(64, 10), 80);
    }

    #[test]
    fn a_stack_written_to_its_bottom_is_written_whole() {
        assert_eq!(written_after(64, 64), 512);
    }

    #[test]
    #[should_panic(expected = "the loader's stack is in words")]
    fn a_stack_not_in_words_is_a_bug() {
        let mut stack = [0u64; 2];
        unsafe { fill(stack.as_mut_ptr() as u64 + 4, 8) };
    }
}
