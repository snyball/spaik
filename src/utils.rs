//! Miscellaneous Utilities

use std::convert::Infallible;

const STACK_SZ: usize = 32;

// Helpful when needing to store a stack on *the* stack.
#[derive(Default)]
#[allow(unused)]
pub struct Stack<T> {
    elems: [T; STACK_SZ],
    top: u8,
}

pub type Success = Result<(), Infallible>;

#[allow(unused)]
impl<T: Copy + Default> Stack<T> {
    pub fn new() -> Stack<T> {
        Default::default()
    }

    pub fn push(&mut self, v: T) {
        if (self.top as usize) >= self.elems.len() {
            panic!("Stack overflow.");
        }
        self.elems[self.top as usize] = v;
        self.top += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.top == 0 {
            return None;
        }
        self.top -= 1;
        Some(self.elems[self.top as usize])
    }

    pub fn len(&self) -> usize {
        self.top as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.elems[..(self.top as usize)].iter().rev()
    }
}

macro_rules! count_args {
    () => { 0 };
    ( $arg:expr ) => { 1 };
    ( $arg:expr, $($tail:expr),* ) => {
        1 + count_args!($($tail),*)
    }
}

macro_rules! from_many {
    ( $to:ty |$v:ident| { $($from:ty => $action:block),+ } ) => {
        $(
            impl From<$from> for $to {
                fn from($v: $from) -> $to {
                    $action
                }
            }
        )+
    }
}

#[allow(unused)]
pub fn is_sorted<T>(xs: &[T]) -> bool
where T: Ord {
    xs.iter()
      .zip(xs.iter().skip(1))
      .all(|(u, v)| u <= v)
}

/// SPAIK uses the convention:
/// ```ignore
/// invalid!(x, y, z) // <function that made them invalid>
/// ```
/// for marking variables that become invalidated, and may have pointers that no
/// longer point to valid data. Do not access any variable after invalid!(...)
/// has marked them, even if rustc will let you!
///
/// **Do not rely on all invalidated variables being documented**
macro_rules! invalid {
    ($($pv:ident),+) => {{ $(drop($pv);)+ }};
}
