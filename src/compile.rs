//! SPAIK Compiler

use crate::nuke::{NkSum, NkRef};
use crate::nkgc::{PV, SymID, SymIDInt, Cons};
use crate::r8vm::{R8VM, r8c, ArgSpec};
use crate::r8vm::r8c::Op as R8C;
use crate::chasm::{ChOp, ChASM, ChASMOpName, Lbl};
use crate::chasm;
use crate::error::{Error, ErrorKind, Source};
use crate::ast::{Value, ValueKind, ListBuilder, Arith2, Cmp2};
use crate::ast;
use crate::r8vm::r8c::OpName::*;
use std::collections::HashMap;
use fnv::{FnvHashMap, FnvHashSet};
use std::hash::Hash;
use std::mem;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static LAMBDA_COUNT: AtomicUsize = AtomicUsize::new(0);
lazy_static! {
    static ref LABEL_CNT: Mutex<HashMap<String, usize>> =
        Mutex::new(HashMap::new());
}

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
    (Quasi, "sys::quasi"),
    (Unquote, "sys::unquote"),
    (USplice, "sys::usplice"),
    (Obj, "obj"),
    (Struct, "struct"),
    (Loop, "loop"),
    (Cdr, "cdr"),
    (Car, "car"),
    (Cons, "cons"),
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

pub fn arg_parse(args: &Value) -> Result<(Vec<SymID>, ArgSpec), Error> {
    let mut syms = Vec::new();
    let mut spec = ArgSpec::default();
    let mut it = args.iter();
    let mut modifier = None;
    let mut had_opt = false;

    for arg in it.by_ref() {
        if let Value { kind: ValueKind::Symbol(sym), .. } = arg {
            use Builtin::*;
            match Builtin::from_sym(*sym) {
                Some(x @ ArgOptional) => {
                    modifier = Some(x);
                    had_opt = true;
                }
                Some(x @ ArgRest) => modifier = Some(x),
                Some(ArgBody) => modifier = Some(ArgRest),
                _ => {
                    match modifier.take() {
                        Some(ArgOptional) => spec.nopt += 1,
                        Some(ArgRest) => {
                            spec.rest = true;
                            syms.push(*sym);
                            break;
                        }
                        None if had_opt => return Err(ErrorKind::SyntaxError {
                            msg: "Normal argument follows &?".to_string()
                        }.into()),
                        None | Some(_) => spec.nargs += 1,
                    }
                    syms.push(*sym);
                }
            }
        } else {
            return Err(ErrorKind::SyntaxError {
                msg: format!("Did not expect: {}", arg),
            }.into());
        }
    }

    if it.next().is_some() {
        return Err(ErrorKind::SyntaxError {
            msg: "Additional argument follows &rest".to_string(),
        }.into());
    }

    Ok((syms, spec))
}

fn quasi_transform(root: Value) -> Result<Value, Error> {
    enum Elem {
        MaybeQuoted(Value),
        Unquoted(Value)
    }
    use Builtin::*;
    use Elem::*;

    if root.is_atom() {
        return Ok(lisp_qq!(Quote ,root))
    }

    let root_src = root.src.clone();
    let mut lisb = ListBuilder::new();
    lisb.push_sym(Append.sym(), root.src.clone());
    let mut li = Vec::new();
    macro_rules! flush {() => {{
        if !li.is_empty() {
            let mut sub_lisb = ListBuilder::new();
            sub_lisb.push_sym(List.sym(), root_src.clone());
            for arg in li.drain(..) {
                match arg {
                    MaybeQuoted(arg) if arg.is_atom() => {
                        let mut lisb = ListBuilder::new();
                        lisb.push_sym(Quote.sym(), arg.src.clone());
                        lisb.push(arg);
                        sub_lisb.push(lisb.get());
                    }
                    Unquoted(arg) | MaybeQuoted(arg) => sub_lisb.push(arg),
                }
            }
            lisb.push(sub_lisb.get());
        }
    }}}
    for arg in root.into_iter() {
        if let Some(bt) = arg.op().and_then(Builtin::from_sym) {
            match bt {
                Unquote => li.push(Unquoted(raise_inner(bt.sym(), arg)?)),
                USplice => {
                    flush!();
                    lisb.push(raise_inner(bt.sym(), arg)?);
                },
                Quasi => {
                    let inner = raise_inner(bt.sym(), arg)?;
                    li.push(MaybeQuoted(
                        lisp_qq!(Quote ,(quasi_transform(inner)?))));
                },
                _ => li.push(MaybeQuoted(quasi_transform(arg)?)),
            }
        } else {
            li.push(MaybeQuoted(quasi_transform(arg)?));
        }
    }
    flush!();
    Ok(lisb.get())
}

/// Given an expression of the form (outer <inner>), return <inner>
fn raise_inner(op: SymID, v: Value) -> Result<Value, Error> {
    let src = v.src.clone();
    let nargs = v.nargs();
    match v.into_args().next() {
        Some(arg) if nargs == 1 => Ok(arg),
        _ => Err(error!(ArgError,
                        expect: ArgSpec::normal(1),
                        got_num: nargs as u32)
                 .op(op).src(src))
    }
}

type VarSet = FnvHashSet<(SymID, BoundVar)>;

struct ClzScoper<'a> {
    lowered: VarSet,
    env: Env,
    outside: &'a EnvMap,
}

impl ClzScoper<'_> {
    pub fn new(args: Vec<SymID>, outside: &EnvMap) -> ClzScoper {
        ClzScoper {
            lowered: FnvHashSet::default(),
            env: Env::new(args),
            outside
        }
    }

    fn find_quasi(&mut self, ast: &Value) -> Result<(), Error> {
        match ast.bt_op() {
            Some(Builtin::Unquote) => for arg in ast.args() {
                self.find(arg)?;
            },
            _ => for arg in ast.args() {
                self.find_quasi(arg)?;
            }
        }
        Ok(())
    }

    pub fn handle_app<'z>(&mut self,
                          op: SymID,
                          args: impl Iterator<Item = &'z Value>
    ) -> Result<(), Error> {
        if let Some(&var) = self.outside.get(&op) {
            self.lowered.insert((op, var));
        }
        for arg in args {
            self.find(arg)?;
        }
        Ok(())
    }

    pub fn find(&mut self, ast: &Value) -> Result<(), Error> {
        if let Some(bt) = ast.bt_op() {
            match bt {
                Builtin::Quasi => for arg in ast.args() {
                    self.find_quasi(arg)?
                },
                Builtin::Quote => (),
                Builtin::Let => {
                    let ast::Let(pairs, rest) = ast.bt_let()?;
                    let len = pairs.len();
                    for ast::LetBinding(name, ..) in pairs {
                        self.env.defvar(name);
                    }
                    self.find(rest)?;
                    self.env.pop(len);
                }
                Builtin::Lambda => {
                    let ast::Lambda(ast::ArgList(_, args), body) =
                        ast.bt_lambda()?;
                    for arg in args {
                        self.env.defvar(arg);
                    }
                    self.find(body)?;
                }
                _ => self.handle_app(bt.sym(), ast.args())?,
            }
        } else if let Some(op) = ast.op() {
            self.handle_app(op, ast.args())?;
        } else if ast.is_atom() {
            if let ValueKind::Symbol(var) = ast.kind {
                if self.env.get_idx(var).is_some() {
                } else if let Some(&bound) = self.outside.get(&var) {
                    self.lowered.insert((var, bound));
                } else if var == Builtin::Nil.sym() {
                } else {
                    return err_src!(ast.src.clone(), UndefinedVariable, var);
                }
            }
        } else {
            for part in ast.iter() {
                self.find(part)?;
            }
        }
        Ok(())
    }

    pub fn scope_body(mut self, body: &Value) -> Result<VarSet, Error> {
        self.find(body)?;
        Ok(self.lowered)
    }
}

pub unsafe fn pv_to_value(v: PV, src: &Source) -> Value {
    let kind = match v {
        PV::Sym(sym) => ValueKind::Symbol(sym),
        PV::Nil => ValueKind::Nil,
        PV::Int(x) => ValueKind::Int(x),
        PV::Bool(x) => ValueKind::Bool(x),
        PV::Real(x) => ValueKind::Real(x),
        PV::Ref(p) => match (*p).match_ref() {
            NkRef::Cons(Cons { car, cdr }) =>
                ValueKind::Cons(Box::new(pv_to_value(*car, src)),
                                Box::new(pv_to_value(*cdr, src))),
            NkRef::String(s) => ValueKind::String(s.clone()),
            NkRef::PV(v) => pv_to_value(*v, src).kind,
            x => unimplemented!("{:?}", x),
        }
        x => unimplemented!("{:?}", x)
    };
    Value { kind, src: src.clone() }
}

/**
 * Compile Value into R8C code.
 */
pub struct R8Compiler<'a> {
    asm: ChASM,
    pub(crate) estack: Vec<Env>,
    loops: Vec<LoopCtx>,
    consts: Vec<NkSum>,
    // FIXME: This can probably be removed
    symtbl: HashMap<SymID, isize>,
    vm: &'a mut R8VM,
    source_tbl: SourceList,
}

#[derive(Clone, Copy)]
struct LoopCtx {
    start: Lbl,
    end: Lbl,
    ret: bool,
    height: usize,
}

impl<'a> R8Compiler<'a> {
    pub fn new(vm: &'a mut R8VM) -> R8Compiler<'a> {
        R8Compiler {
            asm: Default::default(),
            estack: Default::default(),
            consts: Default::default(),
            symtbl: Default::default(),
            loops: Default::default(),
            source_tbl: Default::default(),
            vm
        }
    }

    pub fn set_source(&mut self, src: Source) {
        match self.source_tbl.last() {
            Some((_, last_src)) if *last_src == src => (),
            _ => {
                let idx = self.asm.len();
                self.source_tbl.push((idx, src));
            }
        }
    }

    pub fn compile_top(&mut self,
                       ret: bool,
                       code: &Value) -> Result<(), Error> {
        self.estack.push(Env::empty());
        self.compile_seq(ret, code.iter())
    }

    pub fn globals(&self) -> Option<impl Iterator<Item = (&SymID, &usize)>> {
        self.estack.first().map(|s| s.iter_statics())
    }

    fn compile_seq<'z>(&mut self,
                       ret: bool,
                       seq: impl Iterator<Item = &'z Value>
    ) -> Result<(), Error> {
        let mut args: Vec<_> = seq.collect();
        let last = args.pop();
        for arg in args.iter() {
            self.compile(false, arg)?;
        }
        if let Some(v) = last {
            self.compile(ret, v)?;
        } else if ret {
            self.asm.op(chasm!(NIL));
        }
        Ok(())
    }

    pub fn enter_fn(&mut self,
                    args: &[SymID],
                    spec: ArgSpec) -> Result<(), Error> {
        let mut env = Env::none();
        if spec.has_env() {
            env.defvar(Builtin::LambdaObject.sym());
        }
        for arg in args {
            env.defvar(*arg);
        }
        env.defvar(Builtin::IP.sym());
        env.defvar(Builtin::Frame.sym());
        self.estack.push(env);
        if spec.is_special() {
            self.asm.op(chasm!(SAV 2));
            if spec.has_opt() {
                self.asm.op(chasm!(TOP spec.nargs));
                self.asm.op(chasm!(JV 1, spec.nopt));
                for _ in 0..spec.nopt {
                    self.asm.op(chasm!(NIL));
                }
            }
            if spec.has_body() {
                self.asm.op(chasm!(TOP spec.nargs + spec.nopt));
                self.asm.op(chasm!(VLIST));
            }
            if spec.has_env() {
                self.asm.op(chasm!(CLZEXP));
            }
            self.asm.op(chasm!(RST));
        }
        Ok(())
    }

    // TODO: TCE, where (VCALL rec, n) becomes (FRAME 2; VJMP rec)
    //       FRAME tears down the current frame and replaces it with
    //       the `n` items that were pushed before it runs.
    //       VJMP jumps to a symbol.
    //       After static linking, VCALL and VJMP become CALL and JMP
    //       This optimization should happen during a pre-processing
    //       step where terminals are replaced with:
    //         `(<ζ>::become terminal-fn args...)`
    pub fn compile_fn(&mut self, _name: SymID, args: &Value, body: &Value) -> Result<(ArgSpec, Vec<SymID>), Error> {
        let (args, spec) = arg_parse(args)?;
        self.enter_fn(&args, spec)?;
        self.compile_seq(true, body.iter())?;
        self.leave_fn();
        Ok((spec, args))
    }

    fn leave_fn(&mut self) {
        self.asm.op(chasm!(RET));
        self.estack.pop();
    }

    /**
     * Reduces nested applications of `not`
     *
     * # Arguments
     *
     * - `code` : The root of the AST tree to be reduced.
     *
     * # Examples
     *
     * - `(not <_>)` ➙ `(true, <_>)`
     * - `(not (not (not <_>)))` ➙ `(true, <_>)`
     * - `(not (not (not (not <_>))))` ➙ `(false, <_>)`
     *
     * Where the boolean represents whether or not the expression
     * has been negated.
     *
     * # Errors
     *
     * Returns an `ArgError` if `not` is given fewer or more than 1 argument.
     *
     * # Algorithm
     *
     * [Video explanation.](https://youtu.be/ohDB5gbtaEQ?t=65)
     */
    pub fn argument_clinic(mut code: &Value) -> Result<(bool, &Value), Error> {
        let mut flipped = false;
        while let Some(op) = code.op() {
            if Builtin::from_sym(op) != Some(Builtin::Not) {
                break;
            }
            let args: Vec<_> = code.args().collect();
            match &args[..] {
                [head] => code = head,
                _ => return Err(error!(ArgError,
                                       expect: ArgSpec::normal(1),
                                       got_num: args.len() as u32)
                                .op(op).src(code.src.clone()))
            }
            flipped = !flipped;
        }
        Ok((flipped, code))
    }

    fn bt_if(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        let args: Vec<_> = code.args().collect();
        let (cond, if_true, if_false) = match &args[..] {
            [cond, if_true, if_false] => (cond, if_true, Some(if_false)),
            [cond, if_true] => (cond, if_true, None),
            _ => return Err(error!(ArgError,
                                   expect: ArgSpec::opt(2, 1),
                                   got_num: args.len() as u32)
                            .op(Builtin::If.sym()).src(code.src.clone()))
        };
        let (flipped, cond) = R8Compiler::argument_clinic(cond)?;
        use ValueKind::*;
        let ((jt, jn), cond) = match cond.bt_cmp2() {
            Some(Cmp2::Eq(Value { kind: Int(0), .. }, v)) |
            Some(Cmp2::Eq(v, Value { kind: Int(0), ..})) => ((JZ, JNZ), v),
            _ => ((JT, JN), cond)
        };
        self.compile(true, cond)?;
        let end_lbl = self.asm.label("if_end");
        let if_false_lbl = self.asm.label("if_false");
        let _jmp_loc = if flipped {
            self.asm.op(chasm!(jt if_false_lbl))
        } else {
            self.asm.op(chasm!(jn if_false_lbl))
        };
        self.compile(ret, if_true)?;
        if let Some(if_false) = if_false {
            self.asm_op(chasm!(JMP end_lbl));
            self.asm.mark(if_false_lbl);
            self.compile(ret, if_false)?;
            self.asm.mark(end_lbl);
        } else if ret {
            self.asm_op(chasm!(JMP end_lbl));
            self.asm.mark(if_false_lbl);
            self.asm.op(chasm!(NIL));
            self.asm.mark(end_lbl);
        } else {
            self.asm.mark(if_false_lbl);
        }
        Ok(())
    }

    fn bt_and(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        let mut it = code.args().peekable();
        if it.peek().is_none() {
            self.asm.op(chasm!(BOOL 1));
            return Ok(());
        }
        let end_l = self.asm.label("and_end");
        let and_exit = self.asm.label("and_early_exit");
        while let Some(part) = it.next() {
            let (flip, part) = R8Compiler::argument_clinic(part)?;
            self.compile(it.peek().is_some() || ret, part)?;
            if flip {
                self.asm.op(chasm!(JT and_exit));
            } else {
                self.asm.op(chasm!(JN and_exit));
            }
        }
        self.asm.pop();
        if ret {
            self.asm.op(chasm!(JMP end_l));
            self.asm.mark(and_exit);
            self.asm.op(chasm!(NIL));
            self.asm.mark(end_l);
        } else {
            self.asm.mark(and_exit);
        }
        Ok(())
    }

    fn bt_or(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        let mut it = code.args().peekable();
        if it.peek().is_none() {
            self.asm.op(chasm!(BOOL 0));
            return Ok(());
        }
        let end_l = self.asm.label("or_end");
        for part in code.args() {
            let (flip, part) = R8Compiler::argument_clinic(part)?;
            self.compile(it.peek().is_some() || ret, part)?;
            if ret { self.asm.op(chasm!(DUP)); }
            if flip { self.asm.op(chasm!(JN end_l)); }
            else    { self.asm.op(chasm!(JT end_l)); }
            if ret { self.asm.op(chasm!(POP 1)); }
        }
        if ret { self.asm.op(chasm!(NIL)); }
        self.asm.mark(end_l);
        Ok(())
    }

    fn bt_not(&mut self, code: &Value) -> Result<(), Error> {
        let (flip, code) = R8Compiler::argument_clinic(code)?;
        self.compile(true, code)?;
        if flip {
            self.asm.op(chasm!(NOT));
        }
        Ok(())
    }

    fn with_env<T>(&mut self, f: impl Fn(&mut Env) -> T) -> Result<T, Error> {
        self.estack
            .last_mut()
            .map(f)
            .ok_or_else(|| "No environment".into())
    }

    fn cc_let(&mut self, ret: bool, code: ast::Let) -> Result<(), Error> {
        let ast::Let(pairs, rest) = code;
        let len = pairs.len();
        for ast::LetBinding(name, val, ..) in pairs {
            self.compile(true, val)?;
            self.with_env(|env| env.defvar(name))?;
        }
        self.compile_seq(ret, rest.iter())?;
        if ret {
            self.asm.op(chasm!(POPA 1, len));
        } else {
            self.asm_op(chasm!(POP len));
        }
        self.env_pop(len)
    }

    fn bt_let(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        self.cc_let(ret, code.bt_let()?)
    }

    fn bt_define(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        match code.bt_define()? {
            ast::Define::Var(name, init) =>
                self.define_static(ret, name, init)
                    .map_err(|op| op.op(Builtin::Define.sym())),
            ast::Define::Func(name, ast::ArgList(spec, args), code) => {
                let mut cc = R8Compiler::new(self.vm);
                cc.enter_fn(&args, spec)?;
                cc.compile_seq(true, code.iter())?;
                cc.leave_fn();
                let res = cc.link()?;
                self.vm.add_func(name, res, spec, args);
                if ret {
                    self.asm_op(chasm!(CLZ name, 0));
                }
                Ok(())
            }
        }
    }

    // TODO: What this should eventually compile to
    //   (loop (if (= x 0)
    //             (break))
    //      (println x)
    //      (set x (- x 1)))
    //   (println "Done.")
    //   =>
    //   loop_begin:
    //       mov x
    //       jz loop_end
    //       mov x
    //       syscall println
    //       dec x, 1
    //       jmp loop_begin
    //   loop_end:
    //       constref 0
    //       syscall println
    fn bt_loop<'z>(&mut self,
                   ret: bool,
                   seq: impl Iterator<Item = &'z Value>) -> Result<(), Error> {
        let start = self.asm.label("loop_start");
        let end = self.asm.label("loop_end");
        let height = self.with_env(|env| env.len())?;
        self.loops.push(LoopCtx { start, end, ret, height });
        self.asm.mark(start);
        self.compile_seq(false, seq)?;
        self.asm.op(chasm!(JMP start));
        self.asm.mark(end);
        self.loops.pop();
        Ok(())
    }

    #[inline]
    fn asm_op(&mut self, op: ChOp) {
        self.asm.op(op);
    }

    fn bt_next(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        if code.nargs() == 0 {
            self.bt_loop_next(code)
        } else {
            let args = code.args().collect::<Vec<_>>();
            use ValueKind::*;
            match &args[..] {
                [Value { kind: Symbol(var), src }] => {
                    let bound = self.get_var_idx(*var, src)?;
                    match bound {
                        BoundVar::Local(idx) => self.asm_op(chasm!(NXIT idx)),
                        BoundVar::Env(idx) => {
                            self.asm_op(chasm!(GET idx));
                            let idx = self.with_env(|env| env.anon())?;
                            self.asm_op(chasm!(NXIT idx));
                            self.asm_op(chasm!(POPA 1, 1));
                            self.env_pop(1)?;
                        }
                    }
                }
                [init] => {
                    self.compile(true, init)?;
                    let idx = self.with_env(|env| env.anon())?;
                    self.asm_op(chasm!(NXIT idx));
                    self.asm_op(chasm!(POPA 1, 1));
                    self.env_pop(1)?;
                }
                _ => return Err(error!(ArgError,
                                       expect: ArgSpec::opt(0, 1),
                                       got_num: args.len() as u32)
                                .src(code.src.clone()).op(Builtin::Next.sym()))
            };
            if !ret {
                self.asm_op(chasm!(POP 1));
            }
            Ok(())
        }
    }

    fn bt_loop_next(&mut self, code: &Value) -> Result<(), Error> {
        let outer = self.loops
                        .last()
                        .copied()
                        .ok_or(error_src!(code.src.clone(), OutsideContext,
                                          op: Builtin::Next.sym(),
                                          ctx: Builtin::Loop.sym()))?;
        ArgSpec::none().check(Builtin::Next.sym(), code.nargs())?;
        let LoopCtx { start, height, .. } = outer;
        let dist = self.with_env(|env| env.len())? - height;
        self.asm_op(chasm!(POP dist));
        self.asm_op(chasm!(JMP start));
        Ok(())
    }

    fn bt_break(&mut self, code: &Value) -> Result<(), Error> {
        let outer = self.loops
                        .last()
                        .copied()
                        .ok_or(error_src!(code.src.clone(), OutsideContext,
                                          op: Builtin::Break.sym(),
                                          ctx: Builtin::Loop.sym()))?;
        ArgSpec::opt(0, 1).check(Builtin::Break.sym(), code.nargs())?;
        let args: Vec<_> = code.args().collect();
        let LoopCtx { end, ret, height, .. } = outer;
        let dist = self.with_env(|env| env.len())? - height;
        let popa = |cc: &mut R8Compiler| if dist > 0 {
            cc.asm_op(chasm!(POPA 1, dist-1))
        };
        match &args[..] {
            [code] if ret => {
                self.compile(true, code)?;
                popa(self);
            }
            [] if ret => {
                self.asm_op(chasm!(NIL));
                popa(self);
            }
            _ if dist > 0 => self.asm_op(chasm!(POP dist)),
            _ => ()
        }
        self.asm_op(chasm!(JMP end));
        Ok(())
    }

    /**
     * Compiles code that pushes a value onto the stack.
     *
     * # Arguments
     *
     * - `code` : AST root.
     *
     * # Returns
     *
     * The statically known stack-index of the value that
     * will be pushed by `code`.
     *
     * # Note
     *
     * You need to call `env_pop` when the value is known
     * to be removed from the stack.
     */
    #[inline]
    fn push(&mut self, code: &Value) -> Result<usize, Error> {
        self.compile(true, code)?;
        self.with_env(|env| env.anon())
    }

    fn pushit<'z>(&mut self, args: impl Iterator<Item = &'z Value>) -> Result<usize, Error> {
        let mut nargs = 0;
        for arg in args {
            nargs += 1;
            self.push(arg)?;
        }
        Ok(nargs)
    }

    fn env_pop(&mut self, n: usize) -> Result<(), Error> {
        self.with_env(|env| env.pop(n))
    }

    fn gen_call<'z>(&mut self,
                    ret: bool,
                    name: SymID,
                    op: (r8c::OpName, &[chasm::Arg]),
                    spec: ArgSpec,
                    args: impl Iterator<Item = &'z Value>) -> Result<(), Error>
    {
        let nargs = self.pushit(args)?;
        spec.check(name, nargs as u16)?;
        self.asm.add(op.0, op.1);
        self.env_pop(nargs)?;
        if !ret {
            self.asm_op(chasm!(POP 1));
        }
        Ok(())
    }

    // FIXME: This API is a bit weird.
    /// `nargs_idx` is the index in op.1 that holds the number
    /// of arguments. Used in instructions like VCALL, LIST,
    /// CLZCALL, etc.
    fn gen_call_nargs<'z>(&mut self,
                          ret: bool,
                          op: (r8c::OpName, &mut [chasm::Arg]),
                          nargs_idx: usize,
                          args: impl Iterator<Item = &'z Value>) -> Result<(), Error> {
        let nargs = self.pushit(args)?;
        op.1[nargs_idx] = nargs.into();
        self.asm.add(op.0, op.1);
        self.env_pop(nargs)?;
        if !ret {
            self.asm_op(chasm!(POP 1));
        }
        Ok(())
    }

    // FIXME: This function is a bit of a mess because of all the special cases:
    //          (/ x) => (/ 1 x)
    //          (- x) => (- 0 x)
    //          (+ x) => x
    //          (* x) => x
    //          (+) => 0
    //          (*) => 1
    //        The general case:
    //          (op x_0 ... x_n) => (op x_0 (... (op x_n-1 x_n))), n >= 2
    fn binop(&mut self,
             code: &Value,
             bop: (r8c::OpName, &[chasm::Arg])) -> Result<(), Error>
    {
        let mut args = code.args().peekable();
        let op = code.op().unwrap();
        if let Some(fst) = args.next() {
            if args.peek().is_none() {
                match bop.0 {
                    r8c::OpName::DIV => { self.asm.op(chasm!(PUSH 1)); },
                    r8c::OpName::SUB => { self.asm.op(chasm!(PUSH 0)); },
                    r8c::OpName::MUL | r8c::OpName::ADD =>
                        return self.compile(true, fst),
                    _ =>
                        return Err(error!(ArgError,
                                          expect: ArgSpec::rest(2, 0),
                                          got_num: 1)
                                   .src(code.src.clone()).op(op))
                }
                self.with_env(|env| env.anon())?;
                self.compile(true, fst)?;
                self.asm.add(bop.0, bop.1);
            } else {
                self.push(fst)?;
                for arg in args {
                    self.compile(true, arg)?;
                    self.asm.add(bop.0, bop.1);
                }
            }
            self.env_pop(1)?;
        } else {
            match bop.0 {
                r8c::OpName::ADD => { self.asm.op(chasm!(PUSH 0)); },
                r8c::OpName::MUL => { self.asm.op(chasm!(PUSH 1)); },
                _ => return Err(error!(ArgError,
                                       expect: ArgSpec::rest(1, 0),
                                       got_num: 0)
                                .src(code.src.clone()).op(op))
            }
        }
        Ok(())
    }

    fn cmp_binop(&mut self,
                 code: &Value,
                 op: (r8c::OpName, &[chasm::Arg])) -> Result<(), Error>
    {
        let args: Vec<_> = code.args().collect();
        ArgSpec::rest(2, 0).check(code.op().unwrap(),
                                  args.len() as u16)?;
        if args.len() == 2 {
            return self.binop(code, op);
        }
        let end_l = self.asm.label("cmp_end");
        let cmp_exit = self.asm.label("cmp_early_exit");
        let mut it = args.windows(2);
        while let Some(&[u, v]) = it.next() {
            self.compile(true, u)?;
            self.compile(true, v)?;
            self.asm.add(op.0, op.1);
            self.asm_op(chasm!(JN cmp_exit));
        }
        self.asm.pop();
        self.asm.op(chasm!(JMP end_l));
        self.asm.mark(cmp_exit);
        self.asm.op(chasm!(BOOL 0));
        self.asm.mark(end_l);
        Ok(())
    }

    fn get_var_idx(&mut self,
                   var: SymID,
                   src: &Source) -> Result<BoundVar, Error> {
        if let Some(idx) = self.with_env(|env| env.get_idx(var))? {
            return Ok(BoundVar::Local(idx));
        }
        for env in self.estack.iter().rev() {
            if let Some(idx) = env.get_env_idx(var) {
                return Ok(BoundVar::Env(idx as u32))
            }
        }
        if let Some(idx) = self.vm.get_env_global(var) {
            return Ok(BoundVar::Env(idx as u32))
        }
        err_src!(src.clone(), UndefinedVariable, var)
    }

    fn asm_set_var_idx(&mut self, idx: &BoundVar) -> Result<(), Error> {
        match idx {
            BoundVar::Local(idx) => self.asm.op(chasm!(STR *idx)),
            BoundVar::Env(idx) => self.asm.op(chasm!(SET *idx)),
        };
        Ok(())
    }

    fn asm_get_var(&mut self,
                   var: SymID,
                   src: &Source) -> Result<(), Error> {
        match self.get_var_idx(var, src)? {
            BoundVar::Local(idx) => self.asm.op(chasm!(MOV idx)),
            BoundVar::Env(idx) => self.asm.op(chasm!(GET idx)),
        };
        Ok(())
    }

    fn bt_set(&mut self,
              ret: bool,
              code: &Value) -> Result<(), Error> {
        let args = code.args().collect::<Vec<_>>();
        use ValueKind::*;
        use Arith2::*;
        match &args[..] {
            [Value { kind: Symbol(dst), src }, init] => {
                let bound = self.get_var_idx(*dst, src)?;
                if let BoundVar::Local(idx) = bound {
                    let mut inplace_op = |op, val: i64| {
                        self.asm.add(op, &[idx.into(), val.into()]);
                        if ret { self.asm_op(chasm!(MOV idx)) }
                    };
                    match init.bt_arith2() {
                        // Handle (set x (+ x 2)) => INC x, 2
                        //        (set x (+ 1 x)) => INC x, 1
                        //        (set x (- x 1)) => DEC x, 1
                        //        (set x (- 1 x)) => Not special
                        Some(Add(Value { kind: Symbol(sym), .. },
                                 Value { kind: Int(num), .. })) |
                        Some(Add(Value { kind: Int(num), .. },
                                 Value { kind: Symbol(sym), .. })) if sym == dst => {
                            inplace_op(INC, *num);
                            return Ok(())
                        }
                        Some(Sub(Value { kind: Symbol(sym), .. },
                                 Value { kind: Int(num), .. })) if sym == dst => {
                            inplace_op(DEC, *num);
                            return Ok(())
                        }
                        _ => ()
                    }
                }
                self.compile(true, init)?;
                if ret { self.asm_op(chasm!(DUP)) }
                // NOTE!: Currently the variable index has no reason to change
                //        between the call to get_var_idx and asm_set_var_idx.
                //        Should that change this will become invalid:
                self.asm_set_var_idx(&bound)
            }
            [obj, init] => if let Some(get) = obj.bt_get() {
                let ast::Get(vec, idx) = get?;
                self.compile(true, init)?;
                if ret { self.asm_op(chasm!(DUP)) }
                self.compile(true, vec)?;
                self.compile(true, idx)?;
                self.asm_op(chasm!(VSET));
                Ok(())
            } else {
                Err(error!(TypeError,
                           expect: Builtin::Symbol.sym(),
                           got: obj.type_of())
                    .op(Builtin::Set.sym())
                    .src(obj.src.clone(), )
                    .argn(1))
            },
            _ => Err(error!(ArgError,
                            expect: ArgSpec::normal(2),
                            got_num: args.len() as u32)
                     .src(code.src.clone())
                     .op(Builtin::Set.sym()))
        }
    }

    pub fn link(self) -> Result<Linked, Error> {
        let len = self.asm.len() as isize;
        let (asm, labels) = self.asm.link::<R8C>(&self.symtbl, len)?;
        Ok((asm, labels, self.consts, self.source_tbl))
    }

    fn define_static(&mut self,
                     ret: bool,
                     name: SymID,
                     init: &Value) -> Result<(), Error> {
        let mut cc = R8Compiler::new(self.vm);
        cc.estack.push(Env::empty());
        cc.compile(true, init)?;
        let (asm, _, consts, srcs) = cc.link()?;
        let pv = unsafe {
            self.vm.add_and_run(asm, Some(consts), Some(srcs))?
        };
        let idx = self.vm.mem.push_env(pv);
        if ret {
            self.asm.op(chasm!(GET idx));
        }
        self.with_env(|env| env.defenv(name, idx))
    }

    fn bt_define_static(&mut self,
                        ret: bool,
                        code: &Value) -> Result<(), Error> {
        let args = code.args().collect::<Vec<_>>();
        match &args[..] {
            [Value { kind: ValueKind::Symbol(dst), .. }, src] =>
                self.define_static(ret, *dst, src),
            [obj, _] => Err(error!(TypeError,
                                   expect: Builtin::Symbol.sym(),
                                   got: obj.type_of())
                            .src(obj.src.clone())
                            .op(Builtin::DefineStatic.sym()).argn(1)),
            _ => Err(error!(ArgError,
                            expect: ArgSpec::normal(2),
                            got_num: args.len() as u32)
                     .src(code.src.clone())
                     .op(Builtin::DefineStatic.sym()))
        }
    }

    fn compile_value(&mut self, v: &Value) {
        use ValueKind::*;
        match &v.kind {
            Symbol(obj) => { self.asm.op(chasm!(SYM *obj)); },
            Nil => { self.asm.op(chasm!(NIL)); },
            Int(x) => { self.asm.op(chasm!(PUSH *x)); },
            Bool(true) => { self.asm.op(chasm!(BOOL 1)); },
            Bool(false) => { self.asm.op(chasm!(BOOL 0)); },
            Real(x) => { self.asm.op(chasm!(PUSHF (*x).to_bits())); },
            Char(c) => { self.asm.op(chasm!(CHAR *c as u32)); }
            String(s) => {
                let idx = self.consts.len();
                self.consts.push(NkSum::String(s.clone()));
                self.asm.op(chasm!(CONSTREF idx));
            }
            Cons(_, _) => {
                let mut len = 0;
                for arg in v.iter() {
                    self.compile_value(arg);
                    len += 1;
                }
                self.asm.op(chasm!(LIST len));
            }
        }
    }

    fn bt_quote(&mut self, code: &Value) -> Result<(), Error> {
        let args = code.args().collect::<Vec<_>>();
        match &args[..] {
            [obj] => self.compile_value(obj),
            _ => return Err(error!(ArgError,
                                   expect: ArgSpec::normal(1),
                                   got_num: args.len() as u32)
                            .src(code.src.clone()).op(Builtin::Quote.sym()))
        }
        Ok(())
    }

    fn bt_quasi(&mut self, code: &Value) -> Result<(), Error> {
        let qt = quasi_transform(
            raise_inner(Builtin::Quasi.sym(), code.clone())?)?;
        self.compile(true, &qt)
    }

    fn eval_when_compile<'z>(&mut self,
                             seq: impl Iterator<Item = &'z Value>
    ) -> Result<Value, Error> {
        let mut cc = R8Compiler::new(self.vm);
        cc.estack.push(Env::empty());
        cc.compile_seq(true, seq)?;
        let (asm, _, consts, srcs) = cc.link()?;
        let res = unsafe {
            self.vm.add_and_run(asm, Some(consts), Some(srcs))?
        };
        Ok(unsafe { pv_to_value(res, &Source::none()) })
    }

    pub fn bt_eval_when(&mut self, code: &Value) -> Result<Value, Error> {
        use Builtin::*;
        let mut it = code.args();
        let when = it.next()
                     .ok_or(error_src!(code.src.clone(), ArgError,
                                       expect: ArgSpec::rest(1, 0),
                                       got_num: 0)
                            .op(EvalWhen.sym()))?;
        let when_src = when.src.clone();
        let when = when.sym()
                       .ok_or(error_src!(when_src.clone(), TypeError,
                                         expect: Builtin::Symbol.sym(),
                                         got: when.type_of())
                              .argn(1).op(EvalWhen.sym()))?;
        let expect = vec![KwCompile.sym(), KwLoad.sym()];
        match Builtin::from_sym(when) {
            Some(KwCompile) => self.eval_when_compile(it),
            Some(KwLoad) => unimplemented!("eval-when :load is not implemented yet."),
            _ => Err(error!(EnumError,
                            expect,
                            got: when)
                     .src(when_src).argn(1).op(EvalWhen.sym()))
        }
    }

    fn bt_lambda(&mut self, code: &Value) -> Result<(), Error> {
        let ast::Lambda(ast::ArgList(mut spec, mut args), body) =
            code.bt_lambda()?;
        let outside = self.with_env(|env| env.as_map())?;
        let mut body = body.clone();
        self.vm.macroexpand_seq(&mut body)?;
        let clz_scoper = ClzScoper::new(args.clone(), &outside);
        let lowered = clz_scoper.scope_body(&body)?;
        let num = LAMBDA_COUNT.fetch_add(1, Ordering::SeqCst);
        let name = self.vm.mem.symdb.put(format!("<λ>::L{}:{}#{}",
                                                 code.src.line,
                                                 code.src.col,
                                                 num));
        let mut num = 0;
        for (var, bound) in lowered.iter() {
            if let BoundVar::Local(idx) = bound {
                args.push(*var);
                self.asm_op(chasm!(MOV *idx));
                num += 1;
            }
        }
        spec.env = num;
        self.asm_op(chasm!(CLZ name, num));
        let mut cc = R8Compiler::new(self.vm);
        cc.enter_fn(&args, spec)?;
        for (var, bound) in lowered.iter() {
            if let BoundVar::Env(idx) = bound {
                cc.with_env(|env| env.defenv(*var, *idx as usize))?;
            }
        }
        cc.compile_seq(true, body.iter())?;
        if spec.has_env() {
            cc.asm_op(chasm!(CLZAV spec.sum_nargs() + 1, spec.env));
        }
        cc.leave_fn();
        let linked = cc.link()?;
        self.vm.add_func(name, linked, spec, args);
        Ok(())
    }

    // TODO: Find out to synthesize all this argument checking into a macro:
    //     with_args! {
    //         code :: Symbol(var), Int(y), String(z), obj => {
    //             do_thing(var, obj)
    //         }
    //         code :: Symbol(var), Int(y), String(z) => { ... }
    //         code :: Symbol(var), Int(y), String(z), rest... => { ... }
    //     }
    //     From this, with_args! should be able to:
    //       1. Throw invalid number of arguments errors
    //       2. Throw type errors.
    //       3. Match and bind on valid arguments
    //       4. Present `rest` arguments as a &[&Value] slice
    //     Different numbers of arguments are allowed, but types
    //     cannot change, a type in position `n` must always be
    //     the same type for all invocations.
    //
    //     This will clean up a lot of the code for the function-like
    //     intrinsics.
    fn bt_var_idx(&mut self, code: &Value) -> Result<(), Error> {
        let args = code.args().collect::<Vec<_>>();
        match &args[..] {
            [Value { kind: ValueKind::Symbol(var), src }] => {
                let (sym, idx) = match self.get_var_idx(*var, src)? {
                    BoundVar::Local(idx) => (Builtin::KwLocal.sym(), idx),
                    BoundVar::Env(idx) => (Builtin::KwEnv.sym(), idx),
                };
                self.asm_op(chasm!(SYM sym));
                self.asm_op(chasm!(PUSH idx));
                self.asm_op(chasm!(CONS));
            }
            [x] => return Err(error!(TypeError,
                                   expect: Builtin::Symbol.sym(),
                                   got: x.type_of())
                              .src(code.src.clone()).argn(1).op(Builtin::DebugVarIdx.sym())),
            _ => return ArgSpec::normal(1).check(Builtin::DebugVarIdx.sym(),
                                                 args.len() as u16)
        }
        Ok(())
    }

    /**
     * Builtin vector push
     *
     * NOTE: In Lisp, the argument order is (push <vec> <elem>), but in
     *       the asm <vec> and <elem> are flipped, because this lets me do
     *       just a single DUP in cases where VPUSH is expected to return
     *       a value.
     */
    fn bt_vpush(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        let nargs = code.nargs();
        ArgSpec::normal(2).check(Builtin::Push.sym(), nargs)?;
        let mut it = code.args();
        let vec = it.next().unwrap();
        let val = it.next().unwrap();
        self.push(val)?;
        if ret {
            self.asm.op(chasm!(DUP));
        }
        self.push(vec)?;
        self.asm.op(chasm!(VPUSH));
        self.env_pop(nargs as usize)
    }

    fn bt_callcc(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        let args: Vec<_> = code.args().collect();
        match args[..] {
            [funk] => {
                self.compile(true, funk)?;
                self.asm_op(chasm!(CALLCC 0));
                if !ret {
                    self.asm_op(chasm!(POP 1));
                }
            }
            _ => return ArgSpec::opt(1, 1).check(Builtin::CallCC.sym(),
                                                 args.len() as u16)
        };
        Ok(())
    }

    fn bt_char(&mut self, code: &Value) -> Result<(), Error> {
        let v = code.args().next().ok_or(error!(ArgError,
                                                expect: ArgSpec::normal(1),
                                                got_num: 0)
                                         .op(Builtin::Char.sym()))?;
        if let Value { kind: ValueKind::Symbol(s), .. } = v {
            let mut it = self.vm.sym_name(*s).chars();
            let c = it.next().ok_or(error!(CharSpecError, spec: *s))?;
            if it.next().is_some() {
                return err!(CharSpecError, spec: *s)
            }
            let u: u32 = c.into();
            self.asm_op(chasm!(CHAR u));
            Ok(())
        } else {
            Err(error!(TypeError,
                       expect: Builtin::Symbol.sym(),
                       got: code.type_of())
                .op(Builtin::Char.sym())
                .argn(1))
        }
    }

    fn bt_throw(&mut self, code: &Value) -> Result<(), Error> {
        let args: Vec<_> = code.args().collect();
        ArgSpec::normal(1).check(Builtin::Throw.sym(), args.len() as u16)?;
        let v = args[0];
        self.compile(true, v)?;
        self.asm_op(chasm!(UNWIND));
        Ok(())
    }

    fn compile_builtin(&mut self,
                       ret: bool,
                       op: Builtin,
                       code: &Value) -> Option<Result<(), Error>> {
        use Builtin::*;
        let mut gen_call = |opcode, opargs, spec| self.gen_call(ret,
                                                                op.sym(),
                                                                (opcode, opargs),
                                                                spec,
                                                                code.args());
        macro_rules! may_ret {
            ($what:expr) => {{ if ret { $what } else { Ok(()) } }}
        }
        Some(match op {
            Quote => may_ret!(self.bt_quote(code)),
            Quasi => may_ret!(self.bt_quasi(code)),
            Unquote | USplice => err_src!(code.src.clone(), OutsideContext,
                                          ctx: Builtin::Quasi.sym(),
                                          op: op.sym()),
            If => self.bt_if(ret, code),
            Next => self.bt_next(ret, code),
            Break => self.bt_break(code),
            Let => self.bt_let(ret, code),
            And => self.bt_and(ret, code),
            Or => self.bt_or(ret, code),
            Define => self.bt_define(ret, code),
            DefineStatic => self.bt_define_static(ret, code),
            Set => self.bt_set(ret, code),
            Loop => self.bt_loop(ret, code.args()),
            Not => may_ret!(self.bt_not(code)),
            EvalWhen => self.bt_eval_when(code).map(|res| if ret {
                self.compile_value(&res);
            }),
            Throw => self.bt_throw(code),
            Progn => self.compile_seq(ret, code.args()),
            // Next => gen_call(r8c::OpName::NEXT, &[], ArgSpec::normal(1)),
            Lambda => may_ret!(self.bt_lambda(code)),
            Cons => may_ret!(gen_call(r8c::OpName::CONS, &[], ArgSpec::normal(2))),
            Car => may_ret!(gen_call(r8c::OpName::CAR, &[], ArgSpec::normal(1))),
            Cdr => may_ret!(gen_call(r8c::OpName::CDR, &[], ArgSpec::normal(1))),
            // TODO: Convert these to `gen_call_nargs`
            List => may_ret!(gen_call(r8c::OpName::LIST,
                                     &[code.nargs().into()],
                                     ArgSpec::any())),
            Append => may_ret!(gen_call(r8c::OpName::APPEND,
                                       &[code.nargs().into()],
                                       ArgSpec::any())),
            Vector => may_ret!(gen_call(r8c::OpName::VEC,
                                        &[code.nargs().into()],
                                        ArgSpec::any())),
            Push => self.bt_vpush(ret, code),
            Get => may_ret!(gen_call(r8c::OpName::VGET, &[], ArgSpec::normal(2))),
            Len => may_ret!(gen_call(r8c::OpName::LEN, &[], ArgSpec::normal(1))),
            Pop => gen_call(r8c::OpName::VPOP, &[], ArgSpec::normal(1)),
            Add => may_ret!(self.binop(code, (ADD, &[]))),
            Sub => may_ret!(self.binop(code, (SUB, &[]))),
            Div => may_ret!(self.binop(code, (DIV, &[]))),
            Mul => may_ret!(self.binop(code, (MUL, &[]))),
            Gt => may_ret!(self.cmp_binop(code, (GT, &[]))),
            Lt => may_ret!(self.cmp_binop(code, (LT, &[]))),
            Lte => may_ret!(self.cmp_binop(code, (LTE, &[]))),
            Gte => may_ret!(self.cmp_binop(code, (GTE, &[]))),
            Eq => may_ret!(self.cmp_binop(code, (EQL, &[]))),
            Eqp => may_ret!(self.cmp_binop(code, (EQLP, &[]))),
            DebugVarIdx => may_ret!(self.bt_var_idx(code)),
            Char => may_ret!(self.bt_char(code)),
            CallCC => self.bt_callcc(ret, code),
            _ => return None
        })
    }

    #[inline]
    pub fn compile_atom(&mut self, atom: &Value) -> Result<(), Error> {
        use ValueKind::*;
        match &atom.kind {
            Int(x) => { self.asm.op(chasm!(PUSH *x)); },
            Symbol(v) => if let Some(Builtin::Nil) = Builtin::from_sym(*v) {
                self.asm.op(chasm!(NIL));
            } else if self.vm.sym_name(*v).starts_with(':') {
                self.asm_op(chasm!(SYM *v));
            } else if let Err(e) = self.asm_get_var(*v, &atom.src) {
                if self.vm.get_func(*v).is_some() {
                    self.asm.op(chasm!(CLZ *v, 0));
                } else {
                    return Err(e);
                }
            }
            String(p) => {
                let idx = self.consts.len() as i64;
                self.consts.push(NkSum::String(p.clone()));
                self.asm.op(chasm!(CONSTREF idx));
            }
            Bool(true) => { self.asm.op(chasm!(BOOL 1)); },
            Bool(false) => { self.asm.op(chasm!(BOOL 0)); },
            Nil => { self.asm.op(chasm!(NIL)); },
            Real(x) => { self.asm.op(chasm!(PUSHF (*x).to_bits())); },
            Char(c) => { self.asm.op(chasm!(CHAR *c as u32)); },
            Cons(_, _) => unreachable!("Input should be atomic"),
        }
        Ok(())
    }

    #[inline]
    pub fn compile_app(&mut self,
                       ret: bool,
                       op: SymID,
                       code: &Value) -> Result<(), Error> {
        let mut get_bt = |op| Builtin::from_sym(op).and_then(|bt| {
            self.compile_builtin(ret, bt, code)
        });
        if let Some(res) = get_bt(op) { // Builtin/intrinsic application
            res
        } else if let Some(res) = self.vm.expand(code) { // Macro application
            let code = res?;
            self.compile(ret, &code)
        } else if let Ok(()) = self.asm_get_var(op, &code.src) { // Closure call
            self.with_env(|env| env.anon())?;
            self.gen_call_nargs(ret, (r8c::OpName::CLZCALL,
                                      &mut [0.into()]),
                                0, code.args())?;
            self.env_pop(1)
        } else { // Call to symbol (virtual call)
            self.gen_call_nargs(ret, (r8c::OpName::VCALL,
                                      &mut [op.into(), 0.into()]),
                                1, code.args())
        }
    }

    fn compile(&mut self, ret: bool, code: &Value) -> Result<(), Error> {
        self.set_source(code.src.clone());

        if let Some(op) = code.op() {
            self.compile_app(ret, op, code)?;
        } else if code.is_atom() {
            if ret {
                return self.compile_atom(code);
            }
        } else if let Some(lambda_bind) = code.bt_lambda_bind() {
            self.cc_let(ret, lambda_bind?)?;
        } else {
            let mut it = code.iter();
            let op = it.next().unwrap();
            if op.is_atom() {
                return Err(error!(TypeError,
                                  expect: Builtin::Lambda.sym(),
                                  got: op.type_of(),)
                           .src(op.src.clone()).argn(0).op(Builtin::Apply.sym()))
            }
            self.compile(true, op)?;
            self.with_env(|env| env.anon())?; // closure
            self.gen_call_nargs(ret, (r8c::OpName::CLZCALL,
                                      &mut [0.into()]),
                                0, it)?;
            self.env_pop(1)?;
        }
        Ok(())
    }
}
