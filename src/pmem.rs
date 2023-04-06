//! Program Memory

#![allow(dead_code)]

use std::{alloc::{realloc, Layout, handle_alloc_error}, mem::{size_of, align_of}};

use crate::{r8vm::r8c::Op, nuke::malloc};

struct PMem {
    mem: *mut Op,
    sz: usize,
    len: usize,
    ip: *mut Op,
}

impl PMem {
    pub fn new(sz: usize) -> Self {
        let mem = unsafe { malloc(sz) };
        Self { mem, sz, len: 0, ip: mem }
    }

    pub fn fit(&mut self, fit: usize) {
        let new_sz = (self.sz << 1).max(self.sz + fit);
        unsafe {
            let ipd = self.ip.sub(self.mem as usize) as usize;
            let layout = Layout::array::<Op>(self.sz).unwrap();
            let mem = realloc(self.mem as *mut u8,
                              layout,
                              size_of::<Op>() * new_sz) as *mut Op;
            if mem.is_null() {
                handle_alloc_error(layout);
            }
            self.mem = mem;
            self.sz = new_sz;
            self.ip = self.mem.add(ipd);
        }
    }

    pub fn push(&mut self, from: &[Op]) {
        if self.len + from.len() > self.sz {
            self.fit(from.len())
        }
    }
}
