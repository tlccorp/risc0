// Copyright 2023 RISC Zero, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![doc = include_str!("../README.md")]
#![cfg_attr(all(not(feature = "std"), target_os = "zkvm"), no_std)]
#![allow(unused_variables)]
#![feature(alloc_error_handler)]

pub mod abi;
pub mod memory;
#[macro_use]
pub mod syscall;
#[cfg(target_os="zkvm")]
mod bump_alloc;
extern crate alloc;

#[cfg(target_os = "zkvm")]
use core::arch::asm;

pub const WORD_SIZE: usize = core::mem::size_of::<u32>();
pub const PAGE_SIZE: usize = 1024;

/// Standard IO file descriptors for use with sys_read and sys_write.
pub mod fileno {
    pub const STDIN: u32 = 0;
    pub const STDOUT: u32 = 1;
    pub const STDERR: u32 = 2;
    pub const JOURNAL: u32 = 3;
}

#[allow(dead_code)]
fn _fault() -> ! {
    #[cfg(target_os = "zkvm")]
    unsafe {
        asm!("sw x0, 1(x0)")
    };
    unreachable!();
}

#[allow(dead_code)]
fn abort(msg: &str) -> ! {
    unsafe {
        syscall::sys_panic(msg.as_ptr(), msg.len());
    }

    // As a fallback for non-compliant hosts, issue an illegal instruction.
    #[allow(unreachable_code)]
    _fault()
}

#[cfg(all(not(feature = "std"), target_os = "zkvm"))]
mod handlers {
    use core::{alloc::Layout, panic::PanicInfo};

    #[panic_handler]
    fn panic_fault(panic_info: &PanicInfo) -> ! {
        if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
            crate::abort(s)
        } else {
            crate::abort("panic occurred");
        }
    }

    #[alloc_error_handler]
    fn alloc_fault(_layout: Layout) -> ! {
        crate::abort("Memory allocation failure")
    }
}

