//! Miscellaneous Utilities

#[macro_export]
macro_rules! map {
    ( $($k:expr => $v:expr),* $(,)* ) => {{
        let mut m = HashMap::new();
        $(
            m.insert($k, $v);
        )*
        m
    }};
}

#[macro_export]
macro_rules! set {
    [ $($v:expr),* $(,)* ] => {{
        let mut m = HashSet::new();
        $(
            m.insert($v);
        )*
        m
    }};
}

const STACK_SZ: usize = 32;

// Helpful when needing to store a stack on *the* stack.
#[derive(Default)]
pub struct Stack<T> {
    elems: [T; STACK_SZ],
    top: u8,
}

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

#[macro_export]
macro_rules! count_args {
    () => { 0 };
    ( $arg:ident ) => { 1 };
    ( $arg:ident, $($tail:ident),* ) => {
        1 + count_args!($($tail),*)
    }
}

macro_rules! from_many {
    ( $to:ty |$v:ident| { $($from:ty => $action:block),+ } ) => {
        $(
            impl<'a> From<$from> for $to {
                fn from($v: $from) -> $to {
                    $action
                }
            }
        )+
    }
}

pub fn is_sorted<T>(xs: &[T]) -> bool
where T: Ord {
    xs.iter()
      .zip(xs.iter().skip(1))
      .all(|(u, v)| u <= v)
}

#[macro_export]
macro_rules! minto {
    ($($v:expr),+) => {
        &[$($v.into()),+]
    };
}
