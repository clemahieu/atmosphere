use verified::bridge::{SwitchDecision, TrustedBridge};

pub struct Bridge {}

impl TrustedBridge for Bridge {
    fn set_switch_decision(decision: SwitchDecision) {
        let switch_decision = unsafe {
            &mut *crate::get_current_cpu_field_ptr!(switch_decision, SwitchDecision)
        };
        *switch_decision = decision;
    }
}
