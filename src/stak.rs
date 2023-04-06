#![allow(dead_code)]

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

struct Stak<T> {
    ebp: *mut T,
    top: *mut T,
    buf: *mut T,
    sz: usize,
}

impl<T> Stak<T> {
    pub fn new(sz: usize) -> Stak<T> {
        let layout = Layout::array::<T>(sz).unwrap();
        let buf = unsafe { alloc(layout) } as *mut T;
        if buf.is_null() {
            handle_alloc_error(layout);
        }
        Stak { ebp: buf,
               top: buf,
               buf,
               sz }
    }
}

impl<T> Drop for Stak<T> {
    fn drop(&mut self) {
        let layout = Layout::array::<T>(self.sz).unwrap();
        unsafe { dealloc(self.buf as *mut u8, layout) }
    }
}
