//! Miscellaneous Utilities

use std::convert::Infallible;
pub use ahash::AHashMap as HMap;
pub use ahash::AHashSet as HSet;

pub type Success = Result<(), Infallible>;

macro_rules! count_args {
    () => { 0 };
    ( $arg:expr ) => { 1 };
    ( $arg:expr, $($tail:expr),* ) => {
        1 + count_args!($($tail),*)
    }
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
    ($($pv:ident),+) => {{}};
}

#[allow(unused_macros)]
macro_rules! vm_assert {
    ($vm:expr, $ex:expr) => {
        assert!($vm.eval::<bool,_>($ex).unwrap(), $ex)
    };
}
