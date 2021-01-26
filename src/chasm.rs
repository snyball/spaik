// ChASM /ˈkæz(ə)m/, an assembler

use crate::nkgc::SymID;
use std::collections::HashMap;
use std::fmt;
use crate::error::{Error, ErrorKind};
use ErrorKind::*;
use std::convert::{TryInto, TryFrom};
use fnv::FnvHashMap;

macro_rules! chasm_primitives {
    ($($t:ident),+) => {
        #[allow(non_camel_case_types)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum ASMPV {
            $($t($t)),+
        }

        impl fmt::Display for ASMPV {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
                match self { $(ASMPV::$t(v) => write!(f, "{}", v)),+ }
            }
        }

        $(impl From<$t> for ASMPV {
            fn from(v: $t) -> ASMPV { ASMPV::$t(v) }
        })+

        fn try_into_asmpv<T: $(TryFrom<$t> + )+>(pv: ASMPV) -> Result<T, Error> {
            match pv {
                $(ASMPV::$t(v) => v
                  .try_into()
                  .map_err(|_| ConversionError { from: stringify!($t),
                                                 to: std::any::type_name::<T>(),
                                                 val: format!("{}", v) }.into())),+
            }
        }

        $(impl From<$t> for Arg {
            fn from(v: $t) -> Arg { Arg::ASMPV(ASMPV::$t(v)) }
        })+

        $(impl std::convert::TryFrom<ASMPV> for $t {
            type Error = crate::error::Error;
            fn try_from(v: ASMPV) -> Result<Self, Self::Error> {
                try_into_asmpv::<$t>(v)
            }
        })+
    }
}

chasm_primitives![u8, i8,
                  u16, i16,
                  u32, i32,
                  u64, i64,
                  usize, isize];

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Lbl(u32, &'static str);

impl fmt::Display for Lbl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}#{}", self.1, self.0)
    }
}

#[derive(Debug, Clone)]
pub enum Arg {
    Lbl(Lbl),
    ASMPV(ASMPV),
    Func(SymID)
}

impl From<Lbl> for Arg {
    fn from(v: Lbl) -> Self { Arg::Lbl(v) }
}
impl From<SymID> for Arg {
    fn from(v: SymID) -> Self { Arg::ASMPV(v.id.into()) }
}

#[derive(Debug, Clone)]
pub struct ChOp {
    id: u16,
    args: Vec<Arg>,
}

impl ChOp {
    pub fn new(id: u16, args: Vec<Arg>) -> ChOp {
        ChOp { id, args }
    }
}

impl fmt::Display for ChOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let args = self.args
                       .iter()
                       .map(|v| format!("{:?}", v))
                       .collect::<Vec<_>>()
                       .join(", ");
        write!(f, "{} {}", self.id, args)
    }
}

pub trait ASMOp {
    // fn from_id(op: u16, args: &[i64]) -> Result<Self, String>
    //     where Self: std::marker::Sized;
    fn read(op: u16, args: &[ASMPV]) -> Result<Self, Error>
        where Self: std::marker::Sized;
    fn name(&self) -> &'static str;
    fn args(&self) -> Vec<ASMPV>;
}

pub trait ChASMOpName {
    fn dialect(&self) -> &'static str;
    fn id(&self) -> u16;
    fn from_num(num: u16) -> Result<Self, Error>
        where Self: std::marker::Sized;
    fn from_str(s: &str) -> Option<Self>
        where Self: std::marker::Sized;
}

#[macro_export]
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

            #[repr(u16)]
            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub enum OpName {
                $($en),+
            }

            impl $crate::chasm::ChASMOpName for OpName {
                fn dialect(&self) -> &'static str { stringify!($name) }
                fn id(&self) -> u16 {
                    unsafe { std::mem::transmute(*self) }
                }
                fn from_num(id: u16) -> Result<OpName, $crate::error::Error> {
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

            // const NAME: &'static str = stringify!($name);
        }

        impl $crate::chasm::ASMOp for $name::Op {
            fn read(op: u16, args: &[ASMPV]) ->
                Result<$name::Op, $crate::error::Error>
            {
                use std::convert::TryInto;
                use $crate::error::ErrorKind::*;
                match $name::OpName::from_num(op)? {
                    $($name::OpName::$en => match args {
                        [$($arg),*] => Ok($name::Op::$en($((*$arg).try_into()?),*)),
                        _ => Err(SomeError {
                            msg: format!("Not enough arguments for enum variant: {}", op)
                        }.into())
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
        }

        impl std::fmt::Display for $name::Op {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) ->
                Result<(), std::fmt::Error>
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

#[derive(Debug, Clone, Default)]
pub struct ChASM {
    ops: Vec<ChOp>,
    label_names: Vec<&'static str>,
    marks: FnvHashMap<u32, isize>,
}

type Linked<ASM> = (Vec<ASM>, FnvHashMap<u32, Lbl>);

impl ChASM {
    pub fn new() -> ChASM { Default::default() }

    /// # Arguments
    /// - xtrn: Functions that have been defined before this unit,
    ///         the mapping is:
    ///         Function symbol -> Position in program memory
    /// - sz: The total size of program memory
    pub fn link<T: ASMOp>(self,
                          xtrn: &HashMap<SymID, isize>,
                          sz: isize) -> Result<Linked<T>, Error>
    {
        let mut hm = FnvHashMap::with_capacity_and_hasher(self.marks.len(),
                                                          Default::default());
        for (lbl, tgt) in self.marks.iter() {
            hm.insert(*tgt as u32, Lbl(*lbl, self.label_names[*lbl as usize]));
        }
        let labels = self.marks;
        Ok((self.ops
            .into_iter()
            .enumerate()
            .map(|(i, op)| -> Result<T, Error> {
                let link_err = |sym, count| {
                    ErrorKind::LinkError { dst: format!("{}#{}", sym, count),
                                           src: i }
                };
                let args = op.args
                             .into_iter()
                             .map(|arg| match arg {
                                 Arg::Lbl(Lbl(c, s)) =>
                                     labels.get(&(c as u32))
                                           .map(|pos| ASMPV::isize(*pos - (i as isize)))
                                           .ok_or_else(|| link_err(s, c)),
                                 Arg::ASMPV(pv) => Ok(pv),
                                 Arg::Func(s) => xtrn.get(&s)
                                                     .map(|pos| ASMPV::isize(*pos - (i as isize + sz)))
                                                     .ok_or_else(|| link_err("sym", s.id as u32))
                             }).collect::<Result<Vec<ASMPV>, _>>()?;
                T::read(op.id, &args[..])
            }).collect::<Result<_, _>>()?,
            hm))
    }

    pub fn add<T: ChASMOpName>(&mut self, op: T, args: &[Arg]) {
        self.ops.push(ChOp::new(op.id(), Vec::from(args)))
    }

    pub fn op(&mut self, op: ChOp) -> usize {
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
        self.marks.insert(lbl.0 as u32, self.ops.len() as isize);
    }

    pub fn pop(&mut self) {
        self.ops.pop();
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

macro_rules! chasm {
    ($op:ident $($arg:expr),*) => {
        ChOp::new($op.id(), vec![$($arg.into()),*])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_read_op() {
        use crate::r8vm::r8c::Op as R8C;
        use crate::r8vm::r8c::OpName::*;
        assert_eq!(R8C::read(JMP.id(), &[123i32.into()]), Ok(R8C::JMP(123)))
    }

    #[test]
    fn primitive_type_conversions() {
        let pv_big = ASMPV::u32(260);
        let v_big: Result<u8, _> = pv_big.try_into();
        assert_eq!(v_big, Err(Error {
            src: None,
            ty: ConversionError {
                from: "u32",
                to: "u8",
                val: String::from("260")
            }
        }));
    }

    #[test]
    fn assembler() {
        let mut csm = ChASM::new();
        use crate::r8vm::r8c::Op as R8C;
        use crate::r8vm::r8c::OpName::*;
        use crate::chasm::ChASMOpName;
        let sym = SymID::from(1);
        let lbl = csm.label("test");
        csm.mark(lbl);
        csm.op(chasm!(VCALL -10, sym));
        csm.op(chasm!(ADD));
        csm.op(chasm!(ADD));
        csm.op(chasm!(ADD));
        csm.op(chasm!(JMP lbl));
        let xtrn = HashMap::new();
        let (code, _) = csm.link::<R8C>(&xtrn, 0).unwrap();
        assert_eq!(code, vec![R8C::VCALL(-10, 1,),
                              R8C::ADD(),
                              R8C::ADD(),
                              R8C::ADD(),
                              R8C::JMP(-4,)]);
    }
}
