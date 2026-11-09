//! What the instruction set fixes, one implementation per target, selected by target_arch. Each
//! implementation defines the same items with the same specs, so code above this module does not know
//! which ISA it runs on. See design/arch-module/.

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;
