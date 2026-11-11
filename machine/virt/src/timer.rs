// SPDX-License-Identifier: MIT

//! The EL1 physical timer of the generic timer, as a one-shot. design/machine-glue-below-the-kernel/.
//!
//! The timer's condition is met once the physical count reaches CNTP_CVAL_EL0, and its interrupt is
//! asserted for as long as the condition is met while CNTP_CTL_EL0 has ENABLE set and IMASK clear
//! (Arm ARM D12.2.4.1, D24.10.22). The line is a level, so a timer that has fired keeps its
//! interrupt pending until it is disabled or given a later compare value: the one shot is spent by
//! [`disarm`], which the acknowledgement of the timer's interrupt calls.

use crate::instruction::{isb, read, write, System};

/// CNTP_CTL_EL0.ENABLE, bit 0. IMASK, bit 1, stays clear. Arm ARM D24.10.22.
const ENABLE: u64 = 1 << 0;

/// Arms this core's timer to fire `ticks` of the physical count from now.
pub fn arm(ticks: u64) {
    unsafe {
        let now = read(System::Cntpct);
        write(System::CntpCval, now.saturating_add(ticks));
        write(System::CntpCtl, ENABLE);
    }
    isb();
}

/// Disables this core's timer, which withdraws its interrupt.
pub fn disarm() {
    unsafe {
        write(System::CntpCtl, 0);
    }
    isb();
}

#[cfg(test)]
mod tests {
    use crate::instruction::{events, set, Event, System};

    #[test]
    fn arming_sets_the_compare_value_past_the_count_and_then_enables_unmasked() {
        set(System::Cntpct, 0x1_0000_0000);

        super::arm(1000);

        assert_eq!(
            events(),
            [
                Event::Read { register: System::Cntpct },
                Event::Write { register: System::CntpCval, value: 0x1_0000_0000 + 1000 },
                // Arm ARM D24.10.22: ENABLE is bit 0 and IMASK, bit 1, is clear.
                Event::Write { register: System::CntpCtl, value: 0b01 },
                Event::Isb,
            ]
        );
    }

    #[test]
    fn a_slice_past_the_end_of_the_count_stops_at_its_last_value() {
        set(System::Cntpct, u64::MAX - 5);

        super::arm(u64::MAX);

        assert_eq!(events()[1], Event::Write { register: System::CntpCval, value: u64::MAX });
    }

    #[test]
    fn disarming_clears_the_enable() {
        set(System::CntpCtl, 0b101);

        super::disarm();

        assert_eq!(events(), [Event::Write { register: System::CntpCtl, value: 0 }, Event::Isb]);
    }
}
