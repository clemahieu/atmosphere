use vstd::prelude::*;
verus! {

use crate::arch::Registers;

pub struct TrapFrameOption {
    pub reg: Registers,
    pub exists: bool,
}

impl TrapFrameOption {
    pub open spec fn is_Some(&self) -> bool {
        self.exists
    }

    pub open spec fn is_None(&self) -> bool {
        self.exists == false
    }

    pub open spec fn spec_unwrap(&self) -> &Registers
        recommends
            self.is_Some(),
    {
        &self.reg
    }

    pub open spec fn get_Some_0(&self) -> &Registers
        recommends
            self.is_Some(),
    {
        &self.reg
    }

    pub fn is_some(&self) -> (ret: bool)
        ensures
            ret == self.is_Some(),
    {
        self.exists
    }

    pub fn is_none(&self) -> (ret: bool)
        ensures
            ret == self.is_None(),
    {
        self.exists == false
    }

    #[verifier(when_used_as_spec(spec_unwrap))]
    pub fn unwrap(&self) -> (ret: &Registers)
        ensures
            self.get_Some_0() =~= ret,
    {
        &self.reg
    }

    pub fn set_self(&mut self, src: &Registers)
        ensures
            final(self).is_Some(),
            final(self).get_Some_0() =~= src,
    {
        self.exists = true;
        self.reg = *src;
    }

}

} // verus!
