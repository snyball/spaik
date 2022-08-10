use crate::nkgc::SymID;
use crate::chasm::ASMOp;
use crate::sintern::SIntern;
use crate::nuke::NkSum;
use serde::{Serialize, Deserialize};
use std::convert::TryInto;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct SymEntry {
    name_len: u16,
    name: Vec<u8>,
    sym: SymID,
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
pub struct Import {
    path: Vec<SymID>,
    syms: Vec<SymID>,
}

impl Import {
    pub fn new(path: &[SymID], imports: &[SymID]) -> Import {
        Import {
            path: path.to_vec(),
            syms: imports.to_vec()
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ModuleMeta {
    name_len: u32,
    name: Vec<u8>,
    spaik_ver: (u16, u16, u16),
    mod_ver: (u16, u16, u16),
}

#[derive(Deserialize, Serialize, Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum ExportKind {
    Func,
    Macro,
    Var
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
pub struct Export {
    kind: ExportKind,
    name: SymID,
    pos: u32,
}

impl Export {
    pub fn new(kind: ExportKind, name: SymID, pos: u32) -> Export {
        Export { kind, name, pos }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
struct BRWString {
    len: u32,
    buf: Vec<u8>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct LispModule {
    symtbl: Vec<SymEntry>,
    imports: Vec<Import>,
    exports: Vec<Export>,
    strings: Vec<BRWString>,
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
            symtbl,
            exports,
            imports,
            strings,
            pmem,
        }
    }
}
