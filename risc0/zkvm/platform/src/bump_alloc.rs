use core::{
    alloc::{GlobalAlloc, Layout},
};

use crate::{abi,  WORD_SIZE};

struct BumpPointerAlloc;

unsafe impl GlobalAlloc for BumpPointerAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let nwords = layout
            .align_to(WORD_SIZE)
            .expect("Unable to align allocation to word size")
            .pad_to_align()
            .size()
            / WORD_SIZE;

        abi::zkvm_abi_alloc_words(nwords) as *mut u8
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {
        // this allocator never deallocates memory
    }
}

#[global_allocator]
static HEAP: BumpPointerAlloc = BumpPointerAlloc;
