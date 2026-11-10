use verified::bridge::{SwitchDecision, TrustedBridge};

pub struct Bridge {}

impl TrustedBridge for Bridge {
    fn set_switch_decision(decision: SwitchDecision) {
        crate::cpu::get_current().switch_decision = decision;
    }
}
