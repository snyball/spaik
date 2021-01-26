use crate::nkgc::SymID;
use crate::compile::Builtin;
use std::borrow::Cow;

pub trait SymDB {
    fn name(&self, sym: SymID) -> Cow<str>;

    fn put(&mut self, name: &str) -> SymID;
}

#[derive(Default, Clone, Debug)]
pub struct StaticSymDB {}

impl SymDB for StaticSymDB {
    fn name(&self, sym: SymID) -> Cow<str> {
        match Builtin::from_sym(sym) {
            Some(bt) => Cow::Borrowed(bt.get_str()),
            None => Cow::Owned(sym.to_string())
        }
    }

    fn put(&mut self, name: &str) -> SymID {
        panic!("Attempted to create symbol `{}' in FmtSymID", name);
    }
}

pub const SYM_DB: StaticSymDB = StaticSymDB {};
