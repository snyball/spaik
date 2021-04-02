//! String Interner Data Structure

use fnv::FnvHashMap;
use std::hash::Hash;

use crate::sym_db::SymDB;
use crate::nkgc::{SymID, SymIDInt};
use std::convert::TryInto;
use std::collections::HashMap;
use std::slice::Iter;
use std::borrow::Cow;
use std::iter::Zip;
use std::slice;
use std::str;

type StringID = SymIDInt;

/**
 * A bijection between String IDs and Strings, avoids storing more than one copy
 * of the strings.
 */
#[derive(Debug)]
pub struct SIntern<T>
    where T: Into<StringID> + From<StringID> + Default + Copy
{
    start: StringID,
    strings: Vec<(*const u8, usize)>,
    lookup: HashMap<String, T>,
}

impl<T> Default for SIntern<T>
    where T: Into<StringID> + From<StringID> + Default + Copy + Eq + Hash
{
    fn default() -> Self {
        SIntern::new(T::default())
    }
}

impl<T> SIntern<T>
    where T: Into<StringID> + From<StringID> + Default + Copy + Hash + Eq
{
    pub fn new(start: T) -> SIntern<T> {
        SIntern {
            strings: Vec::default(),
            lookup: HashMap::default(),
            start: start.into(),
        }
    }

    pub fn put_ref(&mut self, obj: &str) -> T {
        self.lookup.get(obj).copied().unwrap_or_else(|| unsafe {
            self.put_no_check(String::from(obj))
        })
    }

    pub fn put(&mut self, obj: String) -> T {
        self.lookup.get(&obj).copied().unwrap_or_else(|| unsafe {
             self.put_no_check(obj)
        })
    }

    /**
     * Intern a new string object.
     *
     * SAFETY: If a string that already exists is replaced, this will turn
     * previous symbol IDs into indirect dangling references to the strings that
     * they index in StringInterner::strings.
     */
    unsafe fn put_no_check(&mut self, obj: String) -> T {
        let idx: StringID = self.strings.len().try_into().unwrap();
        let id: T = (idx + self.start).into();
        self.strings.push((obj.as_ptr(), obj.len()));
        self.lookup.insert(obj, id);
        id
    }

    pub fn name(&self, id: T) -> Option<&str> {
        let idx = (id.into() - self.start) as usize;
        self.strings.get(idx).map(|(ptr, len)| unsafe {
            let slice = slice::from_raw_parts(*ptr, *len);
            str::from_utf8(slice).unwrap()
        })
    }

    pub fn get(&self, obj: &str) -> Option<T> {
        self.lookup.get(obj).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (T, &str)> {
        let id_end = self.start + self.strings.len() as StringID;
        let id_it = (self.start..id_end).map(|id| id.into());
        SInternIter { it: id_it.zip(self.strings.iter()) }
    }

    pub fn shrink_to_fit(&mut self) {
        self.strings.shrink_to_fit();
        self.lookup.shrink_to_fit();
    }

    pub fn merge(&mut self, other: SIntern<T>) -> FnvHashMap<T, T> {
        other.iter().map(|(k, v)| (k, self.put_ref(v))).collect()
    }
}

struct SInternIter<'a, R: Iterator<Item = T>, T> {
    it: Zip<R, Iter<'a, (*const u8, usize)>>
}

impl<'a, R: Iterator<Item = T>, T> Iterator for SInternIter<'a, R, T> {
    type Item = (T, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|(id, &(ptr, len))| unsafe {
            let slice = slice::from_raw_parts(ptr, len);
            (id, str::from_utf8(slice).unwrap())
        })
    }
}

impl SymDB for SIntern<SymID> {
    fn name(&self, sym: SymID) -> Cow<str> {
        Cow::Borrowed(self.name(sym).unwrap())
    }

    fn put(&mut self, name: &str) -> SymID {
        self.put(String::from(name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_intern_insertion() {
        for i in 1..100 {
            let mut intern = SIntern::new(i);
            let mut ids = vec![];
            for j in 1..100 {
                ids.push(intern.put(format!("string#{}", j)));
            }

            for (id, num) in ids.iter().zip(1..100) {
                let s = intern.name(*id).unwrap();
                assert_eq!(s, format!("string#{}", num));
            }
        }
    }
}
