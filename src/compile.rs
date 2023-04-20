//! SPAIK Compiler

use crate::nkgc::{PV, SymID, SymIDInt};
use crate::error::Source;
use crate::swym;
use fnv::FnvHashMap;
use std::hash::Hash;
use std::mem;
#[cfg(feature = "freeze")]
use serde::{Serialize, Deserialize};

type VarIdx = u32;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum BoundVar {
    Local(VarIdx),
    Env(VarIdx),
}

#[derive(Default, Debug)]
pub struct Env {
    vars: Vec<SymID>,
    statics: FnvHashMap<SymID, usize>,
}

// FIXME: Statics and locals need to be merged somehow, right
//        now a local (let) always takes precedence over a static
//        variable (intr::define-static)
impl Env {
    pub fn new(args: Vec<SymID>) -> Env {
        let mut env = Env {
            vars: args,
            statics: FnvHashMap::default()
        };
        env.defvar(Builtin::IP.sym());
        env.defvar(Builtin::Frame.sym());
        env
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn none() -> Env {
        Env { vars: vec![], statics: FnvHashMap::default() }
    }

    pub fn defvar(&mut self, var: SymID) {
        self.vars.push(var);
    }

    pub fn anon(&mut self) -> usize {
        let pos = self.vars.len();
        self.vars.push(Builtin::Epsilon.sym());
        pos
    }

    pub fn defenv(&mut self, var: SymID, env_idx: usize) {
        self.statics.insert(var, env_idx);
    }

    pub fn pop(&mut self, n: usize) {
        let new_top = self.vars.len() - n;
        self.vars.truncate(new_top);
    }

    pub fn get_env_idx(&self, var: SymID) -> Option<usize> {
        self.statics.get(&var).copied()
    }

    pub fn get_idx(&self, var: SymID) -> Option<VarIdx> {
        for (i, &v) in self.vars.iter().enumerate().rev() {
            if var == v {
                return Some(i as VarIdx);
            }
        }
        None
    }
}

macro_rules! builtins {
    ($(($sym:ident, $str:expr)),*) => {
        #[repr(u8)]
        #[derive(Debug, PartialEq, Eq, Copy, Clone)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        pub enum Builtin { $($sym),* }

        const NUM_BUILTINS: usize = count_args!($($sym),*);

        pub const BUILTIN_SYMBOLS: [&'static str; NUM_BUILTINS] = [
            $($str),*
        ];

        pub static BUILTIN_SYMS: [swym::Sym; NUM_BUILTINS] = [
            $(crate::swym::Sym::from_static($str)),*
        ];

        static BUILTIN_LOOKUP: phf::Map<&'static str, Builtin> = phf::phf_map! {
            $($str => Builtin::$sym),*
        };

        static BUILTIN_SYM_LOOKUP: phf::Map<&'static str, &'static swym::Sym> = phf::phf_map! {
            $($str => &BUILTIN_SYMS[{
                let idx: u8 = unsafe { mem::transmute(Builtin::$sym) };
                idx as usize
            }]),*
        };

        impl std::fmt::Display for Builtin {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                write!(f, "{}", match self { $(Builtin::$sym => $str),* })
            }
        }
    }
}

builtins! {
    (Unknown, "?"),
    (ConsDot, "."),
    (AyyLmao, "ayy-lmao"),
    (SysLoadPath, "sys/load-path"),
    (SysLoad, "sys/load"),
    (LimitsMacroexpandRecursion, "limits/macroexpand-recursion"),
    (If, "if"),
    (Compile, "compile"),
    (LoopWithEpilogue, "loop-with-epilogue"),
    (ZSendMessage, "<ζ>-send-message"),
    (SymID, "sym-id"),
    (Continuation, "continuation"),
    (Keyword, "keyword"),
    (Join, "join"),
    (Error, "error"),
    (MakeSymbol, "make-symbol"),
    (Pow, "pow"),
    (Modulo, "%"),
    (And, "and"),
    (Or, "or"),
    (Set, "set"),
    (Quote, "quote"),
    (Quasi, "`"),
    (Unquote, ","),
    (USplice, ",@"),
    (Struct, "struct"),
    (Loop, "loop"),
    (Cdr, "cdr"),
    (Car, "car"),
    (Cons, "cons"),
    (Void, "void"),
    (Intr, "intr"),
    (List, "list"),
    (ArgList, "arg-list"),
    (Append, "append"),
    (Vector, "vec"),
    (Get, "get"),
    (Push, "push"),
    (Pop, "pop"),
    (Exit, "exit"),
    (Len, "len"),
    (Lambda, "lambda"),
    (GreekLambda, "λ"),
    (Apply, "apply"),
    (True, "true"),
    (False, "false"),
    (Add, "+"),
    (Sub, "-"),
    (Div, "/"),
    (Mul, "*"),
    (Gt, ">"),
    (Lt, "<"),
    (Lte, "<="),
    (Gte, ">="),
    (Eq, "="),
    (Eqp, "eq?"),
    (Not, "not"),
    (Define, "define"),
    (Progn, "progn"),
    (Catch, "catch"),
    (Throw, "throw"),
    (ArgOptional, "&?"),
    (ArgBody, "&body"),
    (ArgRest, "&rest"),
    (KwPass, ":pass"),
    (KwFail, ":fail"),
    (KwOk, ":ok"),
    (Fail, "fail"),
    (Symbol, "symbol"),
    (Char, "char"),
    (CallCC, "call/cc"),
    (Integer, "integer"),
    (String, "string"),
    (Ref, "ref"),
    (Next, "next"),
    (Break, "break"),
    (Number, "number"),
    (UnsignedInteger, "unsigned-integer"),
    (Float, "float"),
    (Bool, "bool"),
    (HaltFunc, "<ζ>-halt"),
    (IP, "<ζ>-ip"),
    (Frame, "<ζ>-frame"),
    (LambdaObject, "<ζ>-lambda-object"),
    (IterStop, "<ζ>-iter-stop"),
    (ZCore, "<ζ>-core"),
    (Subr, "subr"),
    (Nil, "nil"),
    (Iter, "iter"),
    (Vec2, "vec2"),
    (Vec3, "vec3"),
    (Vec4, "vec4"),
    (Mat2, "mat2"),
    (Mat3, "mat3"),
    (Mat4, "mat4"),
    (Quat, "quat"),
    (Epsilon, "")
}

impl Builtin {
    pub fn from_sym(n: SymID) -> Option<Builtin> {
        let nint = i32::from(n);
        if (0..NUM_BUILTINS as i32).contains(&nint) {
            Some(unsafe { mem::transmute(nint as u8) })
        } else {
            None
        }
    }

    pub fn get_str(&self) -> &'static str {
        let idx: u8 = unsafe { mem::transmute(*self) };
        BUILTIN_SYMBOLS[idx as usize]
    }

    pub fn sym(&self) -> SymID {
        let id: u8 = unsafe { mem::transmute(*self) };
        let id_int: SymIDInt = id.into();
        id_int.into()
    }

    pub(crate) fn swym(&self) -> swym::SymID {
        let id: u8 = unsafe { mem::transmute(*self) };
        let idx: usize = id.into();
        let rf: &'static swym::Sym = &BUILTIN_SYMS[idx];
        swym::SymID::new(rf as *const swym::Sym as *mut swym::Sym)
    }

    pub(crate) fn swym_from_str<S: AsRef<str>>(s: S) -> swym::SymID {
        let rf: &'static swym::Sym = BUILTIN_SYM_LOOKUP[s.as_ref()];
        swym::SymID::new(rf as *const swym::Sym as *mut swym::Sym)
    }

    pub fn to_string(&self) -> String {
        String::from(self.get_str())
    }

    pub fn from<T: AsRef<str>>(s: T) -> Option<Builtin> {
        BUILTIN_LOOKUP.get(s.as_ref()).copied()
    }
}

pub type SourceList = Vec<(usize, Source)>;
