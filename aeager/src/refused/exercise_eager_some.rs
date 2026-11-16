// SPDX-License-Identifier: MIT

//! `exercise_eager`'s Some at an unchanged caller. The biconditional is the operation's ensures
//! at a Some where `new_ok` does not follow. design/refused-claim-per-way/.
//!
//! covers: aeager/src/exercise.rs	exercise_eager	Some
//! refused: unchanged: seen is Some <==> Eager::new_ok(memory, pages, slots, window)

use vstd::prelude::*;

use acall::step::Caller;

use crate::exercise::Exercised;

verus! {

impl super::ExerciseEagerSome for () {
    proof fn unchanged(
        old_caller: Tracked<Caller>,
        final_caller: Tracked<Caller>,
        space: u64,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
        seen: Option<Exercised>,
    ) {
    }
}

} // verus!
