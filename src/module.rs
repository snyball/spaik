use crate::nkgc::SymID;
use crate::chasm::ASMOp;
use crate::sintern::SIntern;
use crate::nuke::NkSum;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct SymEntry {
    name: String,
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

#[derive(Serialize, Deserialize, Debug)]
pub enum Const {
    String(String),
}

#[derive(Serialize, Deserialize, Debug)]
pub struct LispModule {
    symtbl: Vec<SymEntry>,
    imports: Vec<Import>,
    exports: Vec<Export>,
    consts: Vec<Const>,
    pmem: Vec<u8>,
}

impl LispModule {
    pub fn new<ASM>(pmem_in: &[ASM],
                    symtbl_in: &SIntern<SymID>,
                    iconsts: &[NkSum],
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
            symtbl.push(SymEntry { name: name.to_string(), sym });
        }
        let mut consts = vec![];
        consts.extend(iconsts.iter().map(|c| match c {
            NkSum::String(s) => Const::String(s.clone()),
            _ => unimplemented!("Only string constants are supported as module exports"),
        }));
        LispModule {
            symtbl,
            exports,
            imports,
            consts,
            pmem,
        }
    }
}
