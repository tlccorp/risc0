#![cfg_attr(any(target_arch = "riscv32", not(feature = "std")), no_std)]

extern crate alloc;

pub mod core;
#[cfg(all(feature = "hal", not(target_arch = "riscv32")))]
pub mod hal;
mod merkle;
#[cfg(all(feature = "prove", not(target_arch = "riscv32")))]
pub mod prove;
pub mod taps;
#[cfg(feature = "verify")]
pub mod verify;

const MAX_CYCLES_PO2: usize = 20;
pub const MAX_CYCLES: usize = 1 << MAX_CYCLES_PO2;

/// ~100 bits of conjectured security
pub const QUERIES: usize = 50;

pub const INV_RATE: usize = 4;
const FRI_FOLD_PO2: usize = 4;
const FRI_FOLD: usize = 1 << FRI_FOLD_PO2;
const FRI_MIN_DEGREE: usize = 256;

const CHECK_SIZE: usize = INV_RATE * core::fp4::EXT_SIZE;
