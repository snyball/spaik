#![allow(dead_code)]

use crate::nkgc::{SymID, SymIDInt};
use crate::chasm::ASMOp;
use crate::sintern::SIntern;
use crate::nuke::NkSum;
use binwrite::{BinWrite, WriterOption};
use binread::{BinRead, ReadOptions};
use std::{convert::TryInto, io};

/*
use crate::{chasm::Lbl, error::Error, nkgc::SymID, nuke::NkSum, r8vm::{R8VM, r8c}, sintern::SIntern};
use fnv::FnvHashMap;
pub enum Export {
    Func { pos: u32 },
    Macro { pos: u32 },
    Var { val: NkSum }
}

pub struct Import {
    path: Vec<SymID>,
    imports: Vec<SymID>
}

pub struct Version(u32, u32, u32);

pub struct ModuleMeta {
    name: String,
    spaik_ver: String,
    mod_ver: (u32, u32, u32),
}

pub struct LispModule {
    pmem: Vec<r8c::Op>,
    consts: Vec<NkSum>,
    symtbl: SIntern<SymID>,
    labels: FnvHashMap<SymID, FnvHashMap<u32, Lbl>>,
    exports: FnvHashMap<SymID, Export>,
    imports: Vec<Import>,
}
trait ModuleExtract {
    fn freeze(self) -> LispModule;
    fn extract(&self, syms: &[SymID]) -> Result<LispModule, Error>;
}
*/


#[derive(BinWrite, BinRead, Debug, PartialEq, Eq)]
pub struct SymEntry {
    name_len: u16,
    #[br(count = name_len)]
    name: Vec<u8>,

    sym: SymID,
}

impl BinWrite for SymID {
    fn write_options<W>(&self, w: &mut W, wo: &WriterOption) -> Result<(), io::Error>
        where W: io::Write
    {
        BinWrite::write_options(&self.id, w, wo)
    }
}

impl BinRead for SymID {
    type Args = ();

    fn read_options<R>(rd: &mut R, ro: &ReadOptions, _: Self::Args) -> Result<SymID, binread::Error>
        where R: io::Read + io::Seek
    {
        let num: SymIDInt = BinRead::read_options(rd, ro, ())?;
        Ok(num.into())
    }
}

#[derive(BinWrite, BinRead, PartialEq, Eq, Debug)]
pub struct Import {
    path_len: u16,
    #[br(count = path_len)]
    path: Vec<SymID>,

    syms_len: u16,
    #[br(count = syms_len)]
    syms: Vec<SymID>,
}

impl Import {
    pub fn new(path: &[SymID], imports: &[SymID]) -> Import {
        Import {
            path_len: path.len().try_into().unwrap(),
            path: path.to_vec(),
            syms_len: imports.len().try_into().unwrap(),
            syms: imports.to_vec()
        }
    }
}

#[derive(BinWrite, BinRead, Debug)]
pub struct ModuleMeta {
    name_len: u32,
    #[br(count = name_len)]
    name: Vec<u8>,
    spaik_ver: (u16, u16, u16),
    mod_ver: (u16, u16, u16),
}

#[derive(BinRead, Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum ExportKind {
    #[br(magic = 0x00)]
    Func,
    #[br(magic = 0x01)]
    Macro,
    #[br(magic = 0x02)]
    Var
}

pub fn write_export_kind<W>(kind: &ExportKind, writer: &mut W, options: &WriterOption) -> Result<(), io::Error>
    where W: io::Write
{
    let num: u8 = unsafe { std::mem::transmute(*kind) };
    BinWrite::write_options(&num, writer, options)
}

#[derive(BinWrite, BinRead, PartialEq, Eq, Debug)]
pub struct Export {
    #[binwrite(with(write_export_kind))]
    kind: ExportKind,
    name: SymID,
    pos: u32,
}

impl Export {
    pub fn new(kind: ExportKind, name: SymID, pos: u32) -> Export {
        Export { kind, name, pos }
    }
}

#[derive(BinWrite, BinRead, Debug, Clone)]
struct BRWString {
    len: u32,
    buf: Vec<u8>,
}

#[derive(BinWrite, BinRead, Debug)]
#[br(magic = b"SPC\xa4\x01")]
pub struct LispModule {
    meta_len: u32,
    #[br(count = meta_len)]
    meta: Vec<u8>,

    symtbl_len: u32,
    #[br(count = symtbl_len)]
    symtbl: Vec<SymEntry>,

    imports_len: u32,
    #[br(count = imports_len)]
    imports: Vec<Import>,

    exports_len: u32,
    #[br(count = exports_len)]
    exports: Vec<Export>,

    strings_len: u32,
    #[br(count = strings_len)]
    strings: Vec<BRWString>,

    pmem_len: u32,
    #[br(count = pmem_len)]
    pmem: Vec<u8>,
}

impl LispModule {
    pub fn new<ASM>(pmem_in: &[ASM],
                    symtbl_in: &SIntern<SymID>,
                    consts: &[NkSum],
                    imports: Vec<Import>,
                    exports: Vec<Export>) -> LispModule
        where ASM: ASMOp
    {
        let mut pmem = vec![];
        for op in pmem_in.iter() {
            op.write(&mut pmem).unwrap();
        }
        let mut symtbl = vec![];
        for (sym, name) in symtbl_in.iter() {
            let bytes = name.as_bytes();
            symtbl.push(SymEntry { name: Vec::from(bytes),
                                   name_len: bytes.len().try_into().unwrap(),
                                   sym });
        }
        let mut strings = vec![];
        strings.extend(consts.iter().map(|c| match c {
            NkSum::String(s) => {
                let buf = Vec::from(s.as_bytes());
                BRWString { len: buf.len().try_into().unwrap(),
                            buf }
            },
            _ => unimplemented!("Only string constants are supported"),
        }));
        LispModule {
            meta_len: 0,
            meta: vec![],
            symtbl_len: symtbl.len().try_into().unwrap(),
            symtbl,
            exports_len: exports.len().try_into().unwrap(),
            exports,
            imports_len: imports.len().try_into().unwrap(),
            imports,
            strings_len: strings.len().try_into().unwrap(),
            strings,
            pmem_len: pmem.len().try_into().unwrap(),
            pmem,
        }
    }
}

#[derive(BinRead, BinWrite, PartialEq, Eq, Debug)]
#[br(magic = b"TST")]
struct TestThing {
    imports_sz: u32,
    #[br(count = imports_sz)]
    imports: Vec<Import>,
    exports_sz: u32,
    #[br(count = exports_sz)]
    exports: Vec<Export>,
    thing: u32,
    #[br(count = thing)]
    name: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_read_back_module() {
        let thing_in = TestThing {
            imports: vec![],
            imports_sz: 0,
            exports: vec![],
            exports_sz: 0,
            thing: 16,
            name: Vec::from("this is a string".as_bytes()),
        };
        let mut thing_buf = Vec::from("TST".as_bytes());
        thing_in.write(&mut thing_buf).unwrap();
        let mut seeker = io::Cursor::new(thing_buf);
        let thing_out = TestThing::read(&mut seeker).unwrap();
        assert_eq!(thing_in, thing_out);
    }
}
