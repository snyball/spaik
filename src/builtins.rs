//! Builtin Symbols

use crate::{nkgc::SymID, Sym};
use crate::swym;
use std::fmt::{Display, self, LowerHex};
use std::mem;
#[cfg(feature = "freeze")]
use serde::{Serialize, Deserialize};

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
    // NOTE: The zero-length string ε, *must* be a static builtin. Static
    // symbols (e.g builtins) all have `sz: 0`, regardless of length. This
    // system for telling static and dynamically allocated strings apart fails
    // if ɛ can be created during runtime.
    (Epsilon, "")
}

pub trait Hexable {
    fn fmt_hex(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

struct Hex<T>(pub T) where T: LowerHex;

impl<T> Display for Hex<T> where T: LowerHex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0)
    }
}

impl<T> fmt::Debug for Hex<T> where T: LowerHex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0)
    }
}

impl Builtin {
    pub fn from_sym(SymID(p): SymID) -> Option<Builtin> {
        // Check if the pointer `p` is inside the static `BUILTIN_SYMS` array,
        // get its index, and transmute that into a Builtin.
        let p = p as usize;
        let buf = &BUILTIN_SYMS[0] as *const Sym;
        let start = buf as usize;
        let end = unsafe { buf.add(NUM_BUILTINS) } as usize;
        (p >= start && p < end).then(|| unsafe {
            mem::transmute(((p - start) / mem::size_of::<Sym>()) as u8)
        })
    }

    pub fn as_str(&self) -> &'static str {
        let idx: u8 = unsafe { mem::transmute(*self) };
        BUILTIN_SYMBOLS[idx as usize]
    }

    pub(crate) fn sym(&self) -> swym::SymID {
        let id: u8 = unsafe { mem::transmute(*self) };
        let idx: usize = id.into();
        let rf: &'static swym::Sym = &BUILTIN_SYMS[idx];
        swym::SymID::new(rf as *const swym::Sym as *mut swym::Sym)
    }

    pub(crate) fn sym_ref(&self) -> swym::SymRef {
        let id: u8 = unsafe { mem::transmute(*self) };
        let idx: usize = id.into();
        (&BUILTIN_SYMS[idx]).into()
    }

    pub(crate) fn swym_from_str<S: AsRef<str>>(s: S) -> swym::SymID {
        let rf: &'static swym::Sym = BUILTIN_SYM_LOOKUP[s.as_ref()];
        swym::SymID::new(rf as *const swym::Sym as *mut swym::Sym)
    }

    pub fn to_string(&self) -> String {
        String::from(self.as_str())
    }

    pub fn from<T: AsRef<str>>(s: T) -> Option<Builtin> {
        BUILTIN_LOOKUP.get(s.as_ref()).copied()
    }
}

impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.as_str())
    }
}