//! Builtin Symbols

use crate::nkgc::SymID;
use crate::swym;
use std::fmt::{Display, self, LowerHex};
use std::mem;
#[cfg(feature = "freeze")]
use serde::{Serialize, Deserialize};

macro_rules! builtins {
    ($(($sym:ident, $str:expr)),*) => {
        #[repr(u8)]
        #[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
        #[cfg_attr(feature = "freeze", derive(Serialize, Deserialize))]
        pub enum Builtin { $($sym),* }

        const NUM_BUILTINS: usize = count_args!($($sym),*);

        pub const BUILTIN_SYMBOLS: [&'static str; NUM_BUILTINS] = [
            $($str),*
        ];

        pub static BUILTIN_SYMS: [swym::Sym; NUM_BUILTINS] = [
            $(crate::swym::Sym::from_static($str)),*
        ];

        fn get_builtin(s: &str) -> Option<Builtin> {
            Some(match s {
                $($str => Builtin::$sym),*,
                _ => return None
            })
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
    (Intern, "intern"),
    (Pow, "pow"),
    (Modulo, "%"),
    (And, "and"),
    (Or, "or"),
    (Set, "set"),
    (Quote, "quote"),
    (Quasi, "`"),
    (Unquote, ","),
    (USplice, ",@"),
    (Object, "object"),
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
    (Table, "table"),
    (Get, "get"),
    (Push, "push"),
    (Pop, "pop"),
    (Exit, "exit"),
    (Len, "len"),
    (Lambda, "lambda"),
    (GreekLambda, "λ"),
    (Apply, "apply"),
    (MethodCall, "method-call"),
    (True, "true"),
    (False, "false"),
    (Add, "+"),
    (Tag, "tag"),
    (MakeTable, "make-table"),
    (Sub, "-"),
    (Div, "/"),
    (Mul, "*"),
    (Gt, ">"),
    (Lt, "<"),
    (Lte, "<="),
    (Gte, ">="),
    (Eq, "="),
    (Cmp, "cmp"),
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
    (Label, "label"),
    (Char, "char"),
    (Id, "id"),
    (RigidBody, "rigid-body"),
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
    (Callable, "callable"),
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

#[allow(unused)]
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
        let buf = &BUILTIN_SYMS[0] as *const swym::Sym;
        let start = buf as usize;
        let end = unsafe { buf.add(NUM_BUILTINS) } as usize;
        (p >= start && p < end).then(|| unsafe {
            mem::transmute(((p - start) / mem::size_of::<swym::Sym>()) as u8)
        })
    }

    pub fn as_str(&self) -> &'static str {
        let idx: u8 = unsafe { mem::transmute(*self) };
        BUILTIN_SYMBOLS[idx as usize]
    }

    pub(crate) fn sym_id(&self) -> swym::SymID {
        let id: u8 = unsafe { mem::transmute(*self) };
        let idx: usize = id.into();
        let rf: &'static swym::Sym = &BUILTIN_SYMS[idx];
        swym::SymID::new(rf as *const swym::Sym as *mut swym::Sym)
    }

    pub fn sym(&self) -> swym::SymRef {
        let id: u8 = unsafe { mem::transmute(*self) };
        let idx: usize = id.into();
        (&BUILTIN_SYMS[idx]).into()
    }

    pub fn from<T: AsRef<str>>(s: T) -> Option<Builtin> {
        get_builtin(s.as_ref())
    }
}

impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.as_str())
    }
}
