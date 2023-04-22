//! ChASM /ˈkæz(ə)m/, an assembler

use crate::nkgc::SymID;
use std::io::{Read, Write, self};
use std::fmt::{self, Display};
use crate::error::{ErrorKind, Result};
use std::convert::{TryInto, TryFrom};
use fnv::FnvHashMap;

pub type OpCode = u8;

macro_rules! chasm_primitives {
    ($($t:ident),+) => {
        #[allow(non_camel_case_types)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum ASMPV {
            $($t($t)),+
        }

        impl fmt::Display for ASMPV {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self { $(ASMPV::$t(v) => write!(f, "{}", v)),+ }
            }
        }

        $(impl From<$t> for ASMPV {
            fn from(v: $t) -> ASMPV { ASMPV::$t(v) }
        })+

        fn try_into_err(from: &'static str,
                        to: &'static str,
                        val: &dyn std::fmt::Display) -> $crate::error::Error {
            error!(ConversionError, from, to, val: format!("{}", val))
        }

        fn try_into_asmpv<T: $(TryFrom<$t> + )+>(pv: ASMPV) -> Result<T> {
            match pv {
                $(ASMPV::$t(v) => v
                  .try_into()
                  .map_err(|_| try_into_err(stringify!($t),
                                            std::any::type_name::<T>(),
                                            &v).into())),+
            }
        }

        // impl ASMPV {
        //     pub fn add_mut(&mut self, n: isize) -> Result<()> {
        //         match self {
        //             $(ASMPV::$t(ref mut v) => *v += n.try_into()?),+
        //         }
        //         Ok(())
        //     }
        // }

        $(impl From<$t> for Arg {
            fn from(v: $t) -> Arg { Arg::ASMPV(ASMPV::$t(v)) }
        })+

        $(impl std::convert::TryFrom<ASMPV> for $t {
            type Error = crate::error::Error;
            fn try_from(v: ASMPV) -> std::result::Result<Self, Self::Error> {
                try_into_asmpv::<$t>(v)
            }
        })+
    }
}

chasm_primitives![u8, i8,
                  u16, i16,
                  u32, i32,
                  // u64, i64,
                  usize, isize
];

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Lbl(u32, &'static str);

impl fmt::Display for Lbl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}", self.1, self.0)
    }
}

#[derive(Debug, Clone)]
pub enum Arg {
    Lbl(Lbl),
    ASMPV(ASMPV),
}

impl From<Lbl> for Arg {
    fn from(v: Lbl) -> Self { Arg::Lbl(v) }
}
impl From<SymID> for Arg {
    fn from(v: SymID) -> Self { Arg::ASMPV(v.as_int().into()) }
}

#[derive(Debug, Clone)]
pub struct ChOp<T: ChASMOpName> {
    pub id: T,
    pub args: Vec<Arg>,
}

impl<T: ChASMOpName> ChOp<T> {
    pub fn new(id: T, args: Vec<Arg>) -> ChOp<T> {
        ChOp { id, args }
    }
}

impl<T: ChASMOpName + Display> Display for ChOp<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args = self.args
                       .iter()
                       .map(|v| format!("{:?}", v))
                       .collect::<Vec<_>>()
                       .join(", ");
        write!(f, "{} {}", self.id, args)
    }
}

pub trait ASMOp {
    type OpName: ChASMOpName;

    fn new(op: Self::OpName, args: &[ASMPV]) -> Result<Self>
        where Self: std::marker::Sized;
    fn name(&self) -> &'static str;
    fn args(&self) -> Vec<ASMPV>;
    fn write(&self, out: &mut dyn Write) -> io::Result<usize>;
    fn read(inp: &mut dyn Read) -> Result<(Self, usize)>
        where Self: std::marker::Sized;
}

pub trait ChASMOpName {
    fn dialect(&self) -> &'static str;
    fn id(&self) -> OpCode;
    fn from_num(num: OpCode) -> Result<Self>
        where Self: std::marker::Sized;
    fn from_str(s: &str) -> Option<Self>
        where Self: std::marker::Sized;
}

macro_rules! chasm_def {
    ( $name:ident :  $($en:ident($($arg:ident : $targ:ty),*)),+  ) => {
        pub mod $name {
            #[allow(unused_imports)]
            use super::*;
            #[allow(unused_imports)]
            use $crate::chasm::*;

            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub enum Op {
                $($en($($targ),*)),+
            }

            #[repr(u8)]
            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub enum OpName {
                $($en),+
            }

            impl $crate::chasm::ChASMOpName for OpName {
                fn dialect(&self) -> &'static str { stringify!($name) }
                fn id(&self) -> $crate::chasm::OpCode {
                    unsafe { std::mem::transmute(*self) }
                }
                fn from_num(id: $crate::chasm::OpCode) -> Result<OpName> {
                    use $crate::error::ErrorKind::*;
                    if id < count_args!($($en),+) {
                        Ok(unsafe { std::mem::transmute(id) })
                    } else {
                        Err(IDError { id: id as usize }.into())
                    }
                }
                fn from_str(s: &str) -> Option<OpName> {
                    match s {
                        $(stringify!($en) => Some(OpName::$en)),+,
                        _ => None
                    }
                }
            }
        }

        fn op_arg_err(got: usize, expect: usize, name: &'static str) -> Error {
            error!(ArgError,
                   expect: ArgSpec::normal(expect.try_into().unwrap()),
                   got_num: got.try_into().unwrap()).sop(name)
        }

        impl $crate::chasm::ASMOp for $name::Op {
            type OpName = $name::OpName;

            fn new(op: Self::OpName, args: &[ASMPV]) -> Result<$name::Op> {
                use std::convert::TryInto;
                let len = args.len();
                match op {
                    $($name::OpName::$en => if let [$($arg),*] = args {
                        Ok($name::Op::$en($((*$arg).try_into()?),*))
                    } else {
                        Err(op_arg_err(len,
                                       count_args!($($arg),*),
                                       stringify!($en)))
                    }),+
                }
            }

            fn name(&self) -> &'static str {
                match self {
                    $($name::Op::$en(..) => stringify!($en)),+
                }
            }

            fn args(&self) -> Vec<ASMPV> {
                match self {
                    $($name::Op::$en($($arg),*) => {
                        [$((*$arg).into()),*].iter()
                                             .cloned()
                                             .collect::<Vec<ASMPV>>()
                    }),+
                }
            }

            fn write(&self, out: &mut dyn std::io::Write) -> std::io::Result<usize> {
                let mut sz = std::mem::size_of::<$crate::chasm::OpCode>();
                let dscr: usize = unsafe {
                    std::mem::transmute(std::mem::discriminant(self))
                };
                assert!(dscr < 256);
                let op: $crate::chasm::OpCode = dscr as u8;
                out.write_all(&op.to_ne_bytes())?;
                match self {
                    $($name::Op::$en($($arg),*) => {
                        $(let buf = $arg.to_ne_bytes();
                          out.write_all(&buf)?;
                          sz += buf.len();)*
                    })+
                }
                Ok(sz)
            }

            fn read(inp: &mut dyn std::io::Read) -> Result<(Self, usize)> {
                let mut rd_sz = std::mem::size_of::<$crate::chasm::OpCode>();
                let mut op_buf: [u8; 1] = [0];
                inp.read_exact(&mut op_buf)?;
                let op = match $name::OpName::from_num(op_buf[0])? {
                    $($name::OpName::$en => {
                        $(rd_sz += std::mem::size_of::<$targ>();)*
                        $(let mut $arg: [u8; std::mem::size_of::<$targ>()] = Default::default();
                         inp.read_exact(&mut $arg)?;)*
                        $name::Op::$en($(unsafe { std::mem::transmute($arg) }),*)
                    }),+
                };
                Ok((op, rd_sz))
            }
        }

        impl std::fmt::Display for $name::Op {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) ->
                fmt::Result
            {
                use std::convert::TryInto;
                match self {
                    $(
                        $name::Op::$en($($arg),*) => {
                            let args_v = [$((*$arg).try_into().unwrap()),*]
                                .iter()
                                .map(|&s: &i64| s.to_string())
                                .collect::<Vec<_>>();
                            write!(f, "{} {}", stringify!($en).to_lowercase(),
                                   args_v.join(", "))
                        }
                    ),+
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ChASM<T: ASMOp> {
    ops: Vec<ChOp<T::OpName>>,
    label_names: Vec<&'static str>,
    marks: FnvHashMap<u32, isize>,
}

impl<T: ASMOp> Default for ChASM<T> {
    fn default() -> Self {
        Self {
            ops: Default::default(),
            label_names: Default::default(),
            marks: Default::default()
        }
    }
}

pub type LblMap = FnvHashMap<u32, Lbl>;

impl<T: ASMOp> ChASM<T> {
    #[allow(dead_code)]
    pub fn new() -> ChASM<T> {
        Default::default()
    }

    pub fn link_into(self,
                     out: &mut Vec<T>,
                     sz: usize,
                     hm_out: &mut LblMap) -> Result<usize>
    {
        for (lbl, tgt) in self.marks.iter() {
            hm_out.insert((*tgt + sz as isize) as u32,
                          Lbl(*lbl, self.label_names[*lbl as usize]));
        }
        let labels = self.marks;
        let it =
            self.ops
                .into_iter()
                .enumerate()
                .map(|(i, op)| -> Result<T> {
                    let link_err = |sym, count| {
                        ErrorKind::LinkError { dst: format!("{}#{}", sym, count),
                                               src: i }
                    };
                    let args = op.args
                                 .into_iter()
                                 .map(|arg| match arg {
                                     Arg::Lbl(Lbl(c, s)) =>
                                         labels.get(&c)
                                               .map(|pos| ASMPV::i32(*pos as i32 - (i as i32)))
                                               .ok_or_else(|| link_err(s, c)),
                                     Arg::ASMPV(pv) => Ok(pv)
                                 }).collect::<std::result::Result<Vec<ASMPV>, _>>()?;
                    T::new(op.id, &args[..])
                });
        let mut len = 0;
        for asm in it {
            out.push(asm?);
            len += 1;
        }
        Ok(len)
    }

    pub fn add(&mut self, op: T::OpName, args: &[Arg]) {
        self.ops.push(ChOp::new(op, Vec::from(args)))
    }

    pub fn op(&mut self, op: ChOp<T::OpName>) -> usize {
        let len = self.ops.len();
        self.ops.push(op);
        len
    }

    pub fn label(&mut self, text: &'static str) -> Lbl {
        let idx = self.label_names.len();
        self.label_names.push(text);
        Lbl(idx as u32, text)
    }

    pub fn mark(&mut self, lbl: Lbl) {
        self.marks.insert(lbl.0, self.ops.len() as isize);
    }

    pub fn pop(&mut self) {
        self.ops.pop();
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn last_mut(&mut self) -> Option<&mut ChOp<T::OpName>> {
        self.ops.last_mut()
    }
}

macro_rules! chasm {
    ($op:ident $($arg:expr),*) => {
        ChOp::new($op, vec![$($arg.into()),*])
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r8vm::{R8VM, r8c};
    use std::io::Cursor;

    #[test]
    fn read_read_op() {
        use crate::r8vm::r8c::Op as R8C;
        use crate::r8vm::r8c::OpName::*;
        assert_eq!(R8C::new(JMP, &[123i32.into()]), Ok(R8C::JMP(123)))
    }

    #[test]
    fn primitive_type_conversions() {
        let pv_big = ASMPV::u32(260);
        let v_big: Result<u8> = pv_big.try_into();
        assert_eq!(v_big.map_err(|e| e.kind().clone()), Err(ErrorKind::ConversionError {
            from: "u32",
            to: "u8",
            val: String::from("260")
        }));
    }

    #[test]
    fn read_write_asm() {
        let vm = R8VM::no_std();
        let pmem = vm.pmem();
        let mut pmem_out = Vec::<u8>::new();
        for op in pmem.iter() {
            op.write(&mut pmem_out).unwrap();
        }
        let len: u64 = pmem_out.len().try_into().unwrap();
        let mut pmem_in = Cursor::new(pmem_out);
        let mut pmem_2 = Vec::new();
        while pmem_in.position() < len {
            let (op, _) = r8c::Op::read(&mut pmem_in).unwrap();
            pmem_2.push(op);
        }
        assert_eq!(pmem, &pmem_2);
    }
}
