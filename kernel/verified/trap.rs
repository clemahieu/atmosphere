use core::mem::MaybeUninit;
use vstd::prelude::*;
verus! {

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

/// Registers passed to the ISR.
#[repr(C, align(8))]
#[derive(Clone, Copy, Debug)]
pub struct Registers {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,
    // Original interrupt stack frame
    pub error_code: u64,
    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
}

impl Registers {
    #[verifier(external_body)]
    // external_body(gap): builds a value from zeroed memory, which Verus cannot check
    pub const fn zeroed() -> Self {
        unsafe { MaybeUninit::zeroed().assume_init() }
    }

    pub fn new(input: &Registers) -> (ret: Self)
        ensures
            ret =~= *input,
    {
        let ret = Self {
            r15: input.r15,
            r14: input.r14,
            r13: input.r13,
            r12: input.r12,
            rbp: input.rbp,
            rbx: input.rbx,
            r11: input.r11,
            r10: input.r10,
            r9: input.r9,
            r8: input.r8,
            rcx: input.rcx,
            rdx: input.rdx,
            rsi: input.rsi,
            rdi: input.rdi,
            rax: input.rax,
            error_code: input.error_code,
            rip: input.rip,
            cs: input.cs,
            flags: input.flags,
            rsp: input.rsp,
            ss: input.ss,
        };
        ret
    }

    pub fn set_self(&mut self, src: &Registers)
        ensures
            *final(self) == *src,
    {
        *self = *src;
    }
}

} // verus!
