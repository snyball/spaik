//! SPAIK Compiler

use crate::nuke::NkSum;
use crate::nkgc::{PV, SymID, SymIDInt};
use crate::r8vm::R8VM;
use crate::r8vm::r8c::Op as R8C;
use crate::chasm::{ChASM, Lbl};
use crate::error::{Error, Source};
use crate::ast::Value;
use std::collections::HashMap;
use fnv::FnvHashMap;
use std::hash::Hash;
use std::mem;
use std::sync::atomic::AtomicUsize;

static LAMBDA_COUNT: AtomicUsize = AtomicUsize::new(0);

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

type EnvMap = FnvHashMap<SymID, BoundVar>;

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

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn empty() -> Env {
        Env::new(vec![])
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

    pub fn get_idx(&mut self, var: SymID) -> Option<VarIdx> {
        for (i, &v) in self.vars.iter().enumerate().rev() {
            if var == v {
                return Some(i as VarIdx);
            }
        }
        None
    }

    pub fn iter_statics(&self) -> impl Iterator<Item = (&SymID, &usize)> {
        self.statics.iter()
    }

    pub fn as_map(&self) -> FnvHashMap<SymID, BoundVar> {
        let mut map = FnvHashMap::default();
        for (&v, &i) in self.iter_statics() {
            map.insert(v, BoundVar::Env(i as VarIdx));
        }
        for (i, &v) in self.vars.iter().enumerate() {
            map.insert(v, BoundVar::Local(i as VarIdx));
        }
        map
    }
}

#[allow(unused)]
enum Cond {
    EqZero(SymID),
    NeqZero(SymID),
    When(PV),
    Unless(PV),
}

macro_rules! builtins {
    ($(($sym:ident, $str:expr)),*) => {
        #[repr(i32)]
        #[derive(Debug, PartialEq, Eq, Copy, Clone)]
        pub enum Builtin {
            $(
                $sym
            ),*
        }

        impl Builtin {
            pub fn from_sym(n: SymID) -> Option<Builtin> {
                let nint = i32::from(n);
                if (0..count_args!($($sym),*)).contains(&nint) {
                    Some(unsafe { mem::transmute(n) })
                } else {
                    None
                }
            }

            pub const fn num_builtins() -> usize {
                count_args!($($sym),*)
            }


            pub fn get_str(&self) -> &'static str {
                let idx: i32 = unsafe { mem::transmute(*self) };
                BUILTIN_SYMBOLS[idx as usize]
            }

            #[inline]
            pub fn sym(&self) -> SymID {
                let id: SymIDInt = unsafe { mem::transmute(*self) };
                id.into()
            }

            pub fn to_string(&self) -> String {
                String::from(self.get_str())
            }
        }

        impl std::fmt::Display for Builtin {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                write!(f, "{}", match self { $(Builtin::$sym => $str),* })
            }
        }

        pub const BUILTIN_SYMBOLS: [&'static str; count_args!($($sym),*)] = [
            $($str),*
        ];
    }
}

builtins! {
    (Unknown, "?"),
    (ConsDot, "."),
    (AyyLmao, "ayy-lmao"),
    (Unwind, "unwind"),
    (SysLoadPath, "sys/load-path"),
    (SysLoad, "sys/load"),
    (LimitsMacroexpandRecursion, "limits/macroexpand-recursion"),
    (KwUnwind, ":unwind"),
    (If, "if"),
    (Compile, "compile"),
    (Send, "send"),
    (Async, "async"),
    (ZSendMessage, "<ζ>::send-message"),
    (SymID, "sym-id"),
    (Continuation, "continuation"),
    (Keyword, "keyword"),
    (Join, "join"),
    (Error, "error"),
    (MakeSymbol, "make-symbol"),
    (Pow, "pow"),
    (Modulo, "%"),
    (Let, "let"),
    (And, "and"),
    (Or, "or"),
    (Set, "set"),
    (Quote, "quote"),
    (Quasi, "`"),
    (Unquote, ","),
    (USplice, ",@"),
    (Obj, "obj"),
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
    (Call, "call"),
    (Apply, "apply"), // TODO!!!
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
    (DefineStatic, "intr::define-static"),
    (Define, "define"),
    (Progn, "progn"),
    (Catch, "catch"),
    (Throw, "throw"),
    (ArgOptional, "&?"),
    (ArgBody, "&body"),
    (ArgRest, "&rest"),
    (EvalWhen, "eval-when"),
    (KwCompile, ":compile"),
    (KwLoad, ":load"),
    (KwExec, ":exec"),
    (KwLocal, ":local"),
    (KwEnv, ":env"),
    (KwPass, ":pass"),
    (KwFail, ":fail"),
    (KwOk, ":ok"),
    (LispOk, "ok"),
    (Fail, "fail"),
    (Symbol, "symbol"),
    (Char, "char"),
    (CallCC, "call/cc"),
    (Integer, "integer"),
    (String, "string"),
    (Closure, "closure"),
    (Stream, "stream"),
    (Deref, "sys::deref"),
    (Ref, "ref"),
    (New, "new"),
    (Next, "next"),
    (Break, "break"),
    (Number, "number"),
    (UnsignedInteger, "unsigned-integer"),
    (Float, "float"),
    (Bool, "bool"),
    (HaltFunc, "<ζ>::halt"),
    (IP, "<ζ>::ip"),
    (Frame, "<ζ>::frame"),
    (DebugVarIdx, "dbg::var-idx"),
    (LambdaObject, "<ζ>::lambda-object"),
    (IterStop, "<ζ>::iter-stop"),
    (ZCore, "<ζ>::core"),
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

pub type LblLookup = FnvHashMap<u32, Lbl>;

pub type SourceList = Vec<(usize, Source)>;

pub type Linked = (Vec<R8C>,
                   LblLookup,
                   Vec<NkSum>,
                   SourceList);

/**
 * Compile Value into R8C code.
 */
pub struct R8Compiler<'a> {
    asm: ChASM,
    pub(crate) estack: Vec<Env>,
    consts: Vec<NkSum>,
    // FIXME: This can probably be removed
    symtbl: HashMap<SymID, isize>,
    vm: &'a mut R8VM,
    source_tbl: SourceList,
}

impl<'a> R8Compiler<'a> {
    pub fn new(vm: &'a mut R8VM) -> R8Compiler<'a> {
        R8Compiler {
            asm: Default::default(),
            estack: Default::default(),
            consts: Default::default(),
            symtbl: Default::default(),
            source_tbl: Default::default(),
            vm
        }
    }

    pub fn compile_top(&mut self,
                       ret: bool,
                       code: &Value) -> Result<(), Error> {
        unimplemented!()
    }

    pub fn globals(&self) -> Option<impl Iterator<Item = (&SymID, &usize)>> {
        self.estack.first().map(|s| s.iter_statics())
    }

    pub fn link(self) -> Result<Linked, Error> {
        unimplemented!()
    }

    pub fn bt_eval_when(&mut self, code: &Value) -> Result<Value, Error> {
        unimplemented!()
    }
}
