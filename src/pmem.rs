//! Program Memory

use std::{alloc::{realloc, Layout, alloc}, ptr::NonNull};

use crate::r8vm::r8c::Op;

struct PMem {
    mem: NonNull<Op>,
    sz: usize,
    len: usize,
    ip: NonNull<Op>,
}

impl PMem {
    pub fn new(sz: usize) -> Self {
        let layout = Layout::array::<Op>(sz);
        let mem = todo!();
        Self { mem, sz, len: 0, ip: mem }
    }

    pub fn fit(&self, fit: usize) {
        let new_sz = (self.sz << 1).max(self.sz + fit);
        unsafe {
            self.mem = todo!("realloc")
        }
    }

    pub fn push(&mut self, from: &[Op]) {
        if self.len + from.len() > self.sz {
            self.fit(from.len())
        }
    }

}
