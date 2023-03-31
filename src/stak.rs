use std::alloc::{Layout, alloc, dealloc};

struct Stak<T> {
    ebp: *mut T,
    top: *mut T,
    buf: *mut T,
    sz: usize,
}

impl<T> Stak<T> {
    fn new(sz: usize) -> Stak<T> {
        let layout = Layout::array::<T>(sz).unwrap();
        let buf = unsafe { alloc(layout) } as *mut T;
        Stak { ebp: buf,
               top: buf,
               buf,
               sz }
    }
}
