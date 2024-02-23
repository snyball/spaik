//! Formatting for Lisp objects

use crate::nkgc::{ConsElem, ConsIter};
use crate::nuke::*;
use std::fmt;
use crate::utils::{HMap, HSet};
use std::slice::Iter;

pub type VisitSet = HSet<*const NkAtom>;

pub struct FmtWrap<'a, T> where T: ?Sized {
    pub val: &'a T,
}

impl<T> fmt::Display for FmtWrap<'_, T> where T: LispFmt + ?Sized {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut visited = HSet::default();
        self.val.lisp_fmt(&mut visited, f)
    }
}

pub trait LispFmt {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result;

    fn lisp_to_string(&self) -> String {
        format!("{}", FmtWrap { val: self })
    }
}

impl fmt::Display for dyn LispFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.lisp_to_string())
    }
}

impl<T> LispFmt for Vec<T>
    where T: LispFmt
{
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(vec")?;
        if self.is_empty() {
            write!(f, ")")
        } else {
            write!(f, " ")?;
            self.iter().lisp_fmt(visited, f)?;
            write!(f, ")")
        }
    }
}

impl<T> LispFmt for Iter<'_, T>
    where T: LispFmt
{
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.clone().peekable();
        while let Some(item) = it.next() {
            item.lisp_fmt(visited, f)?;
            if it.peek().is_some() {
                write!(f, " ")?;
            }
        }
        Ok(())
    }
}

impl LispFmt for ConsIter {
    fn lisp_fmt(&self,
                visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.clone().peekable();
        write!(f, "(")?;
        while let Some(item) = it.next() {
            if matches!(item, ConsElem::Tail(_)) {
                write!(f, ". ")?;
            }
            item.get().lisp_fmt(visited, f)?;
            if it.peek().is_some() {
                write!(f, " ")?;
            }
        }
        write!(f, ")")
    }
}
