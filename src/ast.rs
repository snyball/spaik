//! Abstract Syntax Tree Tools

use crate::nkgc::Arena;
use crate::nkgc::Cons;
use crate::nkgc::ConsItem;
use crate::nkgc::PV;
use crate::nkgc::SymID;
use crate::error::*;
use crate::nuke::NkRef;
use crate::tok::*;
use crate::perr::*;
use crate::sexpr_parse::string_parse;
use crate::r8vm::{R8VM, ArgInt, ArgSpec};
use crate::compile::Builtin;
use crate::compile::arg_parse;
use crate::sym_db::{SymDB, SYM_DB};
use std::fmt;
use std::fmt::Display;
use std::iter;
use std::ptr;

#[derive(Clone, Debug, PartialEq)]
pub enum ValueKind {
    Int(i64),
    Real(f32),
    String(String),
    Symbol(SymID),
    Cons(Box<Value>, Box<Value>),
    Bool(bool),
    Char(char),
    Nil,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Value {
    pub kind: ValueKind,
    pub src: Source,
}

fn fmt_value(val: &Value, f: &mut fmt::Formatter<'_>, db: &dyn SymDB) -> fmt::Result {
    use ValueKind::*;
    match &val.kind {
        Bool(true) => write!(f, "t"),
        Bool(false) => write!(f, "f"),
        Int(n) => write!(f, "{}", n),
        Real(a) => write!(f, "{}", a),
        String(x) => write!(f, "{:?}", x),
        Symbol(id) => write!(f, "{}", db.name(*id)),
        Char(c) => write!(f, "{}", c),
        Cons(_, _) => {
            write!(f, "(")?;
            let mut head = val;
            loop {
                match &head.kind {
                    Cons(car, cdr) => {
                        fmt_value(car, f, db)?;
                        if cdr.is_nil() {
                            break;
                        }
                        write!(f, " ")?;
                        head = cdr;
                    }
                    _ => {
                        write!(f, " . ")?;
                        fmt_value(head, f, db)?;
                        break;
                    }
                }
            }
            write!(f, ")")?;
            Ok(())
        },
        Nil => write!(f, "nil"),
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_value(self, f, &SYM_DB)
    }
}

pub struct LetBinding<'a>(pub SymID,
                          pub &'a Value,
                          pub &'a Source);
pub struct Let<'a>(pub Vec<LetBinding<'a>>,
                   pub &'a Value);

#[derive(Debug, Clone)]
pub struct ArgList(pub ArgSpec,
                   pub Vec<SymID>);
pub struct Lambda<'a>(pub ArgList,
                      pub &'a Value);

/// An arithmetic operand taking two arguments
pub enum Arith2<'a> {
    Add(&'a Value, &'a Value),
    Sub(&'a Value, &'a Value),
    Mul(&'a Value, &'a Value),
    Div(&'a Value, &'a Value),
}

/// A comparison operand taking two arguments
pub enum Cmp2<'a> {
    Eq(&'a Value, &'a Value),
    Gt(&'a Value, &'a Value),
    Gte(&'a Value, &'a Value),
    Lt(&'a Value, &'a Value),
    Lte(&'a Value, &'a Value),
}

pub struct Get<'a>(pub &'a Value,
                   pub &'a Value);

pub enum Define<'a> {
    Var(SymID, &'a Value),
    Func(SymID, ArgList, &'a Value)
}

impl Value {
    pub fn type_of(&self) -> SymID {
        match self.kind {
            ValueKind::Int(_) => Builtin::Integer.sym(),
            ValueKind::Real(_) => Builtin::Float.sym(),
            ValueKind::String(_) => Builtin::String.sym(),
            ValueKind::Symbol(_) => Builtin::Symbol.sym(),
            ValueKind::Cons(_, _) => Builtin::Cons.sym(),
            ValueKind::Bool(_) => Builtin::Bool.sym(),
            ValueKind::Nil => Builtin::Nil.sym(),
            ValueKind::Char(_) => Builtin::Char.sym(),
        }
    }

    /**
     * Applications like `((lambda (x) (+ x 2)) 2)` are compiled just like
     * `(let ((x 2)) (+ x 2))`.
     */
    pub fn bt_lambda_bind(&self) -> Option<Result<Let>> {
        let mut it = self.iter();
        let nargs = self.nargs();
        let lambda_code = it.next();
        match (lambda_code, lambda_code.map(|x| x.bt_lambda())) {
            (Some(code), _) if code.bt_op() != Some(Builtin::Lambda) => None,
            (_, Some(Ok(Lambda(ArgList(spec, _), _)))) if spec.is_special() => None,
            (_, Some(Ok(Lambda(ArgList(spec, args), body)))) => {
                if let Err(err) = spec.check(Builtin::Lambda.sym(), nargs) {
                    return Some(Err(err))
                }
                Some(Ok(Let(args.iter()
                                .zip(it)
                                .map(|(name, value)| LetBinding(*name, value, &value.src))
                                .collect(),
                            body)))
            }
            (Some(code), Some(Err(err))) if code.bt_op() == Some(Builtin::Lambda) => Some(Err(err)),
            _ => None
        }
    }

    pub fn bt_let(&self) -> Result<Let> {
        let mut it = self.args();
        if let Some(vars) = it.next() {
            let pairs =
                vars.iter()
                    .map(|arg| {
                        let decl: Vec<_> = arg.iter().collect();
                        let err = || {
                            err_src!(arg.src.clone(),
                                     IllegalVariableDeclaration,
                                     decl: arg.clone())
                        };
                        match &decl[..] {
                            [Value { kind: ValueKind::Symbol(sym), src }, val] =>
                                Ok(LetBinding(*sym, val, src)),
                            _ => err()
                        }
                    }).collect::<Result<Vec<_>>>()?;
            Ok(Let(pairs, it.head()))
        } else {
            Err(error!(ArgError,
                       expect: ArgSpec::rest(1, 0),
                       got_num: 0)
                .op(Builtin::Let.sym())
                .src(self.src.clone()))
        }
    }

    pub fn bt_define(&self) -> Result<Define> {
        let op = Builtin::Define.sym();
        let expect = ArgSpec::rest(1, 1);
        let mut it = self.args();
        let src = self.src.clone();
        match it.next() {
            Some(Value { kind: ValueKind::Symbol(var), .. }) => {
                let init = it.next().ok_or(
                    error!(ArgError, expect, got_num: 1).op(op).src(src)
                )?;
                Ok(Define::Var(*var, init))
            }
            Some(fn_def @ Value { kind: ValueKind::Cons(..), .. }) => {
                let mut def_it = fn_def.iter();
                let name = match def_it.next() {
                    Some(Value { kind: ValueKind::Symbol(name), .. }) =>
                        Ok(name),
                    Some(x) => Err(error!(TypeError,
                                          expect: Builtin::Symbol.sym(),
                                          got: x.type_of())
                                   .op(op).argn(1).src(fn_def.src.clone())),
                    _ => unreachable!(),
                }?;
                let (syms, spec) = arg_parse(def_it.head())?;
                Ok(Define::Func(*name, ArgList(spec, syms), it.head()))
            }
            None => Err(error!(ArgError, expect, got_num: 0).op(op).src(src)),
            Some(x) => Err(error!(TypeError,
                                  expect: Builtin::Symbol.sym(),
                                  got: x.type_of())
                           .op(op).src(src).argn(1))
        }
    }

    pub fn bt_get(&self) -> Option<Result<Get>> {
        matches!(self.bt_op(), Some(Builtin::Get)).then(|| {
            ArgSpec::normal(2).check(Builtin::Get.sym(), self.nargs())
                              .map(|_| {
                                  let mut it = self.args();
                                  let vec = it.next().unwrap();
                                  let idx = it.next().unwrap();
                                  Get(vec, idx)
                              })
        })
    }

    pub fn bt_arith2(&self) -> Option<Arith2> {
        self.bt_op().and_then(|bt| {
            let constructor = match bt {
                Builtin::Add => Arith2::Add,
                Builtin::Sub => Arith2::Sub,
                Builtin::Mul => Arith2::Mul,
                Builtin::Div => Arith2::Div,
                _ => return None
            };
            let mut it = self.args();
            let bt = constructor(it.next()?, it.next()?);
            if it.next().is_some() { return None }
            Some(bt)
        })
    }

    pub fn bt_cmp2(&self) -> Option<Cmp2> {
        self.bt_op().and_then(|bt| {
            let constructor = match bt {
                Builtin::Eq => Cmp2::Eq,
                Builtin::Lt => Cmp2::Lt,
                Builtin::Lte => Cmp2::Lte,
                Builtin::Gt => Cmp2::Gt,
                Builtin::Gte => Cmp2::Gte,
                _ => return None
            };
            let mut it = self.args();
            let bt = constructor(it.next()?, it.next()?);
            if it.next().is_some() { return None }
            Some(bt)
        })
    }

    pub fn bt_lambda(&self) -> Result<Lambda> {
        let mut it = self.args();
        let (args, spec) = if let Some(args) = it.next() {
            arg_parse(args)?
        } else {
            return Err(error!(ArgError,
                              expect: ArgSpec::rest(1, 0),
                              got_num: 0)
                       .op(Builtin::Lambda.sym())
                       .src(self.src.clone()))
        };
        Ok(Lambda(ArgList(spec, args), it.head()))
    }

    pub fn new(kind: ValueKind, src: Source) -> Value {
        Value { kind, src }
    }

    pub fn is_nil(&self) -> bool {
        self.kind == ValueKind::Nil
    }

    pub fn is_string(&self) -> bool {
        matches!(self.kind, ValueKind::String(_))
    }

    pub fn is_symbol(&self) -> bool {
        matches!(self.kind, ValueKind::Symbol(_))
    }

    pub fn new_nil() -> Value {
        Value { kind: ValueKind::Nil, src: Source::none() }
    }

    pub fn from_slice(elems: &[Box<Value>]) -> Value {
        let mut li = Value::new_nil();
        li.set_list(elems);
        li
    }

    pub fn from_sym(sym: SymID, src: Source) -> Value {
        Value { kind: ValueKind::Symbol(sym),
                src }
    }

    pub fn cons(car: Box<Value>, cdr: Box<Value>) -> Value {
        let src = car.src.clone();
        Value { kind: ValueKind::Cons(car, cdr),
                src }
    }

    pub fn from_token(vm: &mut R8VM, tok: &Token, file: SourceFileName) -> PResult<Value> {
        let kind = if let Ok(int) = tok.text.parse::<i64>() {
            ValueKind::Int(int)
        } else if let Ok(num) = tok.text.parse::<f32>() { 
            ValueKind::Real(num)
        } else if let Some(string) = tok.inner_str() {
            ValueKind::String(string_parse(&string)?)
        } else if tok.text == "true" {
            ValueKind::Bool(true)
        } else if tok.text == "false" {
            ValueKind::Bool(false)
        } else {
            ValueKind::Symbol(vm.mem.symdb.put_ref(tok.text))
        };
        Ok(Value { kind,
                   src: Source::new(tok.line, tok.col, file) })
    }

    pub fn new_tail(val: Box<Value>) -> Value {
        use ValueKind::*;
        let src = val.src.clone();
        Value::new(Cons(val, Box::new(Value::new(Nil, src.clone()))), src)
    }

    pub fn set_list(&mut self, elems: &[Box<Value>]) {
        let mut node = Value::new_nil();
        for elem in elems.iter().rev() {
            node = Value::cons(elem.clone(), Box::new(node));
        }
        self.src = node.src;
        self.kind = node.kind;
    }

    pub fn pushdown(&mut self, val: Box<Value>) {
        if self.is_nil() {
            return self.set_list(&[val]);
        }
        let mut node = self;
        while let ValueKind::Cons(_, ref mut cdr) = node.kind {
            if cdr.is_nil() {
                *cdr = Box::new(Value::new_tail(val));
                break;
            }
            node = if let ValueKind::Cons(ref mut cdar, _) = cdr.kind {
                cdar
            } else {
                cdr
            }
        }
    }

    pub fn push(&mut self, val: Box<Value>) {
        let mut node = self;
        if node.is_nil() {
            return node.set_list(&[val]);
        }
        while let ValueKind::Cons(_, ref mut cdr) = node.kind {
            if cdr.is_nil() {
                *cdr = Box::new(Value::new_tail(val));
                break;
            }
            node = cdr;
        }
    }

    pub fn to_string(&self, mem: &dyn SymDB) -> String {
        format!("{}", {
            // Dirty hack to pass mem into fmt_pv, as there is no way to just
            // create a fmt::Formatter
            struct PVFmtWrap<'a, 'b> {
                val: &'b Value,
                mem: &'a dyn SymDB,
            }

            impl fmt::Display for PVFmtWrap<'_, '_> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    fmt_value(self.val, f, self.mem)
                }
            }

            PVFmtWrap { val: self, mem }
        })
    }

    pub fn iter(&self) -> ValueIterRef {
        ValueIterRef { done: false,
                       head: self }
    }

    pub fn args(&self) -> ValueIterRef {
        let mut it = self.iter();
        it.next();
        it
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        ValueIterMut { head: Some(self) }
    }

    pub fn args_mut(&mut self) -> impl Iterator<Item = &mut Value> {
        self.iter_mut().skip(1)
    }

    pub fn into_args(self) -> impl Iterator<Item = Value> {
        self.into_iter().skip(1)
    }

    pub fn nargs(&self) -> ArgInt {
        self.args().fold(0, |i, _| i + 1) as ArgInt
    }

    pub fn is_atom(&self) -> bool {
        ! matches!(self.kind, ValueKind::Cons(_, _))
    }

    pub fn bt_op(&self) -> Option<Builtin> {
        self.op().and_then(Builtin::from_sym)
    }

    pub fn bt_sym(&self) -> Option<Builtin> {
        self.sym().and_then(Builtin::from_sym)
    }

    pub fn op(&self) -> Option<SymID> {
        if self.is_atom() {
            return None;
        }

        match self.iter().next() {
            Some(Value { kind: ValueKind::Symbol(sym), .. }) => Some(*sym),
            _ => None
        }
    }

    pub fn sapp(&self) -> Option<(SymID, impl Iterator<Item = &Value>)> {
        self.op().map(|sym| (sym, self.args()))
    }

    pub fn app(&self) -> Option<(&Value, impl Iterator<Item = &Value>)> {
        let mut it = self.iter();
        let op = it.next()?;
        Some((op, it))
    }

    pub fn is_app(&self) -> bool {
        !self.is_atom() && self.iter().next().is_some()
    }

    pub fn into_app(self) -> Option<(Value, impl Iterator<Item = Value>)> {
        let mut it = self.into_iter();
        let op = it.next()?;
        Some((op, it))
    }

    pub fn sym(&self) -> Option<SymID> {
        if let ValueKind::Symbol(s) = self.kind {
            return Some(s);
        }
        None
    }
}

pub struct ValueIter {
    head: Option<Value>,
}

impl Iterator for ValueIter {
    type Item = Value;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(head) = self.head.take() {
            Some(if let ValueKind::Cons(car, cdr) = head.kind {
                self.head = Some(*cdr);
                *car
            } else if head.kind == ValueKind::Nil {
                return None;
            } else {
                self.head = None;
                head
            })
        } else {
            None
        }
    }
}

impl IntoIterator for Value {
    type Item = Value;
    type IntoIter = ValueIter;

    fn into_iter(self) -> Self::IntoIter {
        ValueIter { head: Some(self) }
    }
}

pub struct ValueIterRef<'a> {
    done: bool,
    head: &'a Value,
}

impl<'a> ValueIterRef<'a> {
    pub fn head(self) -> &'a Value {
        self.head
    }
}

impl<'a> Iterator for ValueIterRef<'a> {
    type Item = &'a Value;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        Some(match &self.head.kind {
            ValueKind::Cons(ref car, ref cdr) => {
                self.head = cdr;
                car
            },
            ValueKind::Nil => return None,
            _ => {
                self.done = true;
                self.head
            }
        })
    }
}

pub struct ValueIterMut<'a> {
    head: Option<&'a mut Value>,
}

impl<'a> Iterator for ValueIterMut<'a> {
    type Item = &'a mut Value;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(head) = self.head.take() {
            if let ValueKind::Cons(ref mut car, ref mut cdr) = head.kind {
                self.head = Some(cdr);
                return Some(car)
            }

            if head.kind != ValueKind::Nil {
                return Some(head)
            }
        }

        None
    }
}

impl From<Builtin> for Value {
    fn from(bt: Builtin) -> Self {
        Value::new(ValueKind::Symbol(bt.sym()), Source::none())
    }
}

impl From<Vec<Value>> for Value {
    fn from(seq: Vec<Value>) -> Self {
        let mut root = Value::new_nil();
        for v in seq.into_iter().rev() {
            root = Value::cons(Box::new(v), Box::new(root));
        }
        root
    }
}

pub struct ListBuilder {
    root: Box<Value>,
    last: *mut Value,
}

impl ListBuilder {
    pub fn new() -> ListBuilder {
        let mut lisb = ListBuilder { root: Box::new(Value::new_nil()),
                                     last: ptr::null_mut::<Value>() };
        lisb.last = &mut *lisb.root as *mut Value;
        lisb
    }

    pub fn push(&mut self, v: Value) {
        unsafe {
            let mut new = Box::new(Value::new_nil());
            let last = &mut *new as *mut Value;
            *self.last = Value::cons(Box::new(v), new);
            self.last = last;
        }
    }

    pub fn push_sym(&mut self, sym: SymID, src: Source) {
        self.push(Value { kind: ValueKind::Symbol(sym),
                          src })
    }

    pub fn get(self) -> Value {
        *self.root
    }
}

impl Default for ListBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(unused_macros)]
macro_rules! cons {
    ($x:expr, $y:expr) => (Value::cons(Box::new($x),
                                       Box::new($y)));
}

#[allow(unused_macros)]
macro_rules! lisp_qq {
    ( ( $($li:tt)* ) $($rest:tt)* ) => {
        cons!(lisp_qq!($($li)*), lisp_qq!($($rest)*))
    };
    ( ,( $e:expr ) $($cdr:tt)* ) => {
        cons!($e.into(), lisp_qq!($($cdr)*))
    };
    ( ,$car:tt $($cdr:tt)* ) => {
        cons!($car.into(), lisp_qq!($($cdr)*))
    };
    ( $car:tt $($cdr:tt)* ) => {
        cons!(Builtin::$car.into(), lisp_qq!($($cdr)*))
    };
    () => { Value::new_nil() };
}

pub type Progn = Vec<AST2>;
pub type Prog = Box<AST2>;

#[derive(Debug, Clone)]
pub struct VarDecl(pub SymID, pub Source, pub Prog);

fn nil(src: Source) -> Prog {
    Box::new(AST2 { src, kind: M::Atom(PV::Nil) })
}

fn list(xs: Vec<AST2>, src: Source) -> Prog {
    if xs.is_empty() {
        nil(src)
    } else {
        M::List(xs).boxed(src)
    }
}

#[derive(Debug, Clone)]
pub struct ArgList2(pub ArgSpec,
                    pub Vec<(SymID, Source)>);

#[derive(Debug, Clone)]
pub enum M {
    If(Prog, Option<Prog>, Option<Prog>),
    Atom(PV),
    Progn(Progn),
    // BecomeSelf(Progn),
    // Become(SymID, Progn),
    SymApp(SymID, Progn),
    App(Prog, Progn),
    Lambda(ArgList2, Progn),
    Defvar(SymID, Prog),
    Set(SymID, Prog),
    Defun(SymID, ArgList2, Progn),
    Let(Vec<VarDecl>, Progn),
    Loop(Progn),
    Break(Option<Prog>),
    Next,
    Throw(Prog),
    Var(SymID),

    // Builtin ops
    Not(Prog),
    And(Progn),
    Or(Progn),
    Gt(Prog, Prog),
    Gte(Prog, Prog),
    Lt(Prog, Prog),
    Lte(Prog, Prog),
    Eq(Prog, Prog),
    Eqp(Prog, Prog),
    Add(Progn),
    Sub(Progn),
    Mul(Progn),
    Div(Progn),
    NextIter(Prog),
    Car(Prog),
    Cdr(Prog),
    Cons(Prog, Prog),
    List(Progn),
    Append(Progn),
    Vector(Progn),
    Push(Prog, Prog),
    Get(Prog, Prog),
    Pop(Prog),
    CallCC(Prog),
}

pub enum M2<'a> {
    Add(&'a M, &'a M),
    Sub(&'a M, &'a M),
    Div(&'a M, &'a M),
    Mul(&'a M, &'a M),
}

impl M {
    pub fn boxed(self, src: Source) -> Box<AST2> {
        Box::new(AST2 { kind: self, src })
    }

    pub fn ast(self, src: Source) -> AST2 {
        AST2 { kind: self, src }
    }

    pub fn binary(&self) -> Option<M2> {
        match self {
            M::Add(a) if a.len() == 2 => Some(M2::Add(&a[0].kind, &a[1].kind)),
            M::Sub(a) if a.len() == 2 => Some(M2::Sub(&a[0].kind, &a[1].kind)),
            M::Mul(a) if a.len() == 2 => Some(M2::Mul(&a[0].kind, &a[1].kind)),
            M::Div(a) if a.len() == 2 => Some(M2::Div(&a[0].kind, &a[1].kind)),
            _ => None
        }
    }
}

impl Display for M {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        macro_rules! wargs {
            ($args:expr) => {
                let mut it = $args.into_iter();
                it.next().map(|arg| write!(f, "{arg}"));
                for arg in it { write!(f, " {arg}")?; }
            };
        }
        macro_rules! vop {
            ($op:literal, $args:expr) => {{
                write!(f, "({}", $op)?;
                for arg in $args { write!(f, " {arg}")?; }
            }};
        }
        match self {
            M::If(a, b, c) => {
                write!(f, "(if {a}")?;
                if let Some(b) = b { write!(f, " {b}")?; }
                if let Some(c) = c { write!(f, " {c}")?; }
                write!(f, ")")?;
            },
            M::Atom(a) => write!(f, "{a}")?,
            M::Progn(a) => vop!("progn", a),
            M::SymApp(u, xs) => {
                write!(f, "({u}")?;
                for x in xs.iter() { write!(f, " {x}")? }
                write!(f, ")")?;
            },
            M::App(u, xs) => {
                write!(f, "({u}")?;
                for x in xs.iter() { write!(f, " {x}")? }
                write!(f, ")")?;
            },
            M::Lambda(ArgList2(_, args), progn) => {
                write!(f, "(lambda (")?;
                let mut it = args.iter();
                it.next().map(|arg| write!(f, "{arg:?}"));
                for arg in it {
                    write!(f, " {arg:?}")?;
                }
                wargs!(progn);
            },
            M::Defvar(name, init) => write!(f, "(defvar {name:?} {init})")?,
            M::Set(name, init) => write!(f, "(set {name:?} {init})")?,
            M::Defun(name, ArgList2(_, args), progn) => {
                write!(f, "(define ({name}")?;
                for arg in args { write!(f, " {arg:?}")?; }
                write!(f, ")")?;
                wargs!(progn);
            },
            M::Let(decls, progn) => {
                write!(f, "(let (")?;
                for (i, VarDecl(sym, _, init)) in decls.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "({sym} {init})")?;
                }
                write!(f, ")")?;
                wargs!(progn);
            },
            M::Loop(xs) => vop!("loop", xs),
            M::Break(Some(val)) => write!(f, "(break {val})")?,
            M::Break(None) => write!(f, "(break)")?,
            M::Next => write!(f, "(next)")?,
            M::Throw(x) => write!(f, "(throw {x})")?,
            M::Not(x) => write!(f, "(not {x})")?,
            M::And(xs) => vop!("and", xs),
            M::Or(xs) => vop!("or", xs),
            M::Gt(x, y) => write!(f, "(> {x} {y})")?,
            M::Gte(x, y) => write!(f, "(>= {x} {y})")?,
            M::Lt(x, y) => write!(f, "(< {x} {y})")?,
            M::Lte(x, y) => write!(f, "(<= {x} {y})")?,
            M::Eq(x, y) => write!(f, "(= {x} {y})")?,
            M::Eqp(x, y) => write!(f, "(equal {x} {y})")?,
            M::Add(xs) => vop!("+", xs),
            M::Sub(xs) => vop!("-", xs),
            M::Mul(xs) => vop!("*", xs),
            M::Div(xs) => vop!("/", xs),
            M::NextIter(it) => write!(f, "(next {it})")?,
            M::Car(x) => write!(f, "(car {x})")?,
            M::Cdr(x) => write!(f, "(cdr {x})")?,
            M::Cons(x, y) => write!(f, "(cons {x} {y})")?,
            M::List(xs) => {
                write!(f, "(list")?;
                for x in xs.iter() { write!(f, " {x}")? }
                write!(f, ")")?;
            },
            M::Append(xs) => {
                write!(f, "(append")?;
                for x in xs.iter() { write!(f, " {x}")? }
                write!(f, ")")?;
            },
            M::Vector(xs) => vop!("vec", xs),
            M::Push(vec, elem) => write!(f, "(push {vec} {elem})")?,
            M::Get(vec, idx) => write!(f, "(get {vec} {idx})")?,
            M::Pop(vec) => write!(f, "(pop {vec})")?,
            M::CallCC(funk) => write!(f, "(call/cc {funk})")?,
            M::Var(var) => write!(f, "{var:?}")?,
        }
        Ok(())
    }
}

impl From<PV> for M {
    fn from(pv: PV) -> Self {
        M::Atom(pv)
    }
}

#[derive(Debug, Clone)]
pub struct AST2 {
    pub src: Source,
    pub kind: M,
}

impl AST2 {
    pub fn nil(src: Source) -> AST2 {
        AST2 { src, kind: M::Atom(PV::Nil) }
    }

    pub fn sym(sym: SymID, src: Source) -> AST2 {
        AST2 { src, kind: M::Atom(PV::Sym(sym)) }
    }

    #[allow(dead_code)]
    pub fn is_atom(&self) -> bool {
        if let AST2 { kind: M::Atom(pv), .. } = self {
            pv.is_atom()
        } else {
            false
        }
    }

    pub fn type_of(&self) -> Builtin {
        let unknown = Builtin::Unknown;
        match &self.kind {
            M::Atom(pv) => pv.bt_type_of(),
            M::Add(_) | M::Mul(_) | M::Sub(_) | M::Div(_) => Builtin::Number,
            M::Or(_) | M::And(_) | M::Not(_) | M::Eq(_, _) |
            M::Eqp(_, _) | M::Gt(_, _) | M::Gte(_, _) | M::Lt(_, _) |
            M::Lte(_, _) => Builtin::Bool,
            M::Cdr(_) | M::List(_) | M::Append(_) => Builtin::List,
            M::Vector(_) => Builtin::Vector,
            M::Cons(_, _) => Builtin::Cons,
            M::Lambda(_, _) => Builtin::Lambda,
            M::Progn(xs) | M::Let(_, xs) =>
                xs.last().map(|x| x.type_of()).unwrap_or(unknown),
            M::Defvar(_, x) | M::Set(_, x) => x.type_of(),
            _ => unknown,
        }
    }
}

impl Display for AST2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

pub struct Excavator<'a> {
    mem: &'a Arena, // Arena is read-only while excavating an AST
}

impl<'a> Excavator<'a> {
    pub fn new(mem: &'a Arena) -> Self {
        Excavator { mem }
    }

    pub fn arg_parse(&self, args: PV, src: Source) -> Result<ArgList2> {
        let mut syms = Vec::new();
        let mut spec = ArgSpec::default();
        let mut it = args.iter_src(self.mem, src);
        let mut modifier = None;
        let mut had_opt = false;

        for (item, src) in it.by_ref() {
            let arg = item.car()?;
            if let PV::Sym(sym) = arg {
                use Builtin::*;
                match Builtin::from_sym(sym) {
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
                                syms.push((sym, src));
                                break;
                            }
                            None if had_opt => return Err(ErrorKind::SyntaxError {
                                msg: "Normal argument follows &?".to_string()
                            }.into()),
                            None | Some(_) => spec.nargs += 1,
                        }
                        syms.push((sym, src));
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

        Ok(ArgList2(spec, syms))
    }

    pub fn to_ast(&self, v: PV) -> Result<AST2> {
        self.cav(v)
    }

    fn cav(&self, v: PV) -> Result<AST2> {
        let src = if let PV::Ref(p) = v {
            self.mem.get_tag(p).cloned().unwrap_or_else(Source::none)
        } else {
            Source::none()
        };
        self.dig(v, src)
    }

    fn wrap_one_arg<F>(&self, wrap: F, args: PV, src: Source) -> Result<AST2>
        where F: Fn(Box<AST2>) -> M
    {
        let mut it = args.iter();
        let arg = it.next().ok_or_else(|| error!(ArgError,
                                                 expect: ArgSpec::normal(1),
                                                 got_num: 0)
                                       .src(src.clone()))?;
        let extra = it.count() as u32;
        if extra > 0 {
            Err(error!(ArgError,
                       expect: ArgSpec::normal(1),
                       got_num: 1 + extra)
                .src(src))
        } else {
            Ok(wrap(Box::new(self.dig(arg, src.clone())?)).ast(src))
        }
    }

    fn wrap_maybe_arg<F>(&self, wrap: F, args: PV, src: Source) -> Result<AST2>
        where F: Fn(Option<Prog>) -> M
    {
        let mut it = args.iter();
        let Some(arg) = it.next() else { return Ok(wrap(None).ast(src)) };
        let extra = it.count() as u32;
        if extra > 0 {
            Err(error!(ArgError, expect: ArgSpec::opt(0, 1), got_num: 1 + extra).src(src))
        } else {
            Ok(wrap(Some(Box::new(self.dig(arg, src.clone())?))).ast(src))
        }
    }

    fn wrap_any_args<F>(&self, wrap: F, args: PV, src: Source) -> Result<AST2>
        where F: FnOnce(Vec<AST2>) -> M
    {
        let args: Result<_> = args.into_iter().map(|a| self.dig(a, src.clone()))
                                                .collect();
        Ok(AST2 {
            kind: wrap(args?),
            src,
        })
    }

    fn chain_cmp_op<F>(&self, cmp: F, args: PV, src: Source) -> Result<AST2>
        where F: Fn(Box<AST2>, Box<AST2>) -> M
    {
        let expect = ArgSpec::rest(2, 0);
        let err = |n| {
            let src = &src;
            move || { error!(ArgError, expect, got_num: n).src(src.clone()) }
        };
        let mut it = args.iter();
        let fst = Box::new(self.dig(it.next().ok_or_else(err(0))?, src.clone())?);
        let prev = Box::new(self.dig(it.next().ok_or_else(err(0))?, src.clone())?);
        let icmp = cmp(fst, prev.clone());
        if let Some(nx) = it.next() {
            let nx = Box::new(self.dig(nx, src.clone())?);
            let jcmp = cmp(prev, nx.clone());
            let mut prev = nx;
            let mut cmps = vec![AST2 { src: src.clone(), kind: icmp },
                                AST2 { src: src.clone(), kind: jcmp }];
            for nx in it {
                let nx = Box::new(self.dig(nx, src.clone())?);
                cmps.push(AST2 { src: src.clone(), kind: cmp(prev, nx.clone()) });
                prev = nx;
            }
            Ok(AST2 { src, kind: M::And(cmps) })
        } else {
            Ok(AST2 { src, kind: icmp })
        }
    }

    #[allow(clippy::type_complexity)]
    fn two_and_maybe_one_arg(&self, args: PV, src: Source)
                             -> Result<(Box<AST2>, Box<AST2>, Option<Box<AST2>>)>
    {
        let expect = ArgSpec::opt(2, 1);
        let err = |n| {
            let src = &src;
            move || { error!(ArgError, expect, got_num: n).src(src.clone()) }
        };
        let mut it = args.iter();
        let arg0 = Box::new(self.dig(it.next().ok_or_else(err(0))?, src.clone())?);
        let arg1 = Box::new(self.dig(it.next().ok_or_else(err(1))?, src.clone())?);
        let arg2 = if let Some(v) = it.next() {
            Some(Box::new(self.dig(v, src.clone())?))
        } else {
            None
        };
        let extra = it.count() as u32;
        if extra > 0 {
            Err(err(3 + extra)())
        } else {
            Ok((arg0, arg1, arg2))
        }
    }

    fn two_args(&self, args: PV, src: Source)
                -> Result<(Box<AST2>, Box<AST2>)>
    {
        let expect = ArgSpec::normal(2);
        let err = |n| {
            let src = &src;
            move || { error!(ArgError, expect, got_num: n).src(src.clone()) }
        };
        let mut it = args.iter();
        let arg0 = Box::new(self.dig(it.next().ok_or_else(err(0))?, src.clone())?);
        let arg1 = Box::new(self.dig(it.next().ok_or_else(err(1))?, src.clone())?);
        let extra = it.count() as u32;
        if extra > 0 {
            Err(err(2 + extra)())
        } else {
            Ok((arg0, arg1))
        }
    }

    fn wrap_two_args<F>(&self, wrap: F, args: PV, src: Source) -> Result<AST2>
        where F: FnOnce(Box<AST2>, Box<AST2>) -> M
    {
        let (u, v) = self.two_args(args, src.clone())?;
        Ok(AST2 { kind: wrap(u, v), src })
    }

    fn bt_if(&self, args: PV, src: Source) -> Result<AST2> {
        let (cond, if_true, if_false) = self.two_and_maybe_one_arg(args, src.clone())?;
        Ok(AST2 {
            kind: M::If(cond, Some(if_true), if_false),
            src,
        })
    }

    fn bt_set(&self, args: PV, src: Source) -> Result<AST2> {
        let expect = ArgSpec::normal(2);
        let err = |n| {
            let src = &src;
            move || { error!(ArgError, expect, got_num: n).src(src.clone()) }
        };
        let mut it = args.iter();
        let name = match it.next().ok_or_else(err(0))? {
            PV::Sym(name) => name,
            e => return Err(error!(TypeError,
                                   expect: Builtin::Symbol.sym(),
                                   got: e.type_of()).argn(1))
        };
        let init = Box::new(self.dig(it.next().ok_or_else(err(1))?, src.clone())?);
        let extra = it.count() as u32;
        if extra > 0 {
            Err(err(2 + extra)())
        } else {
            Ok(AST2 { kind: M::Set(name, init), src })
        }
    }

    fn bt_lambda(&self, args: PV, src: Source) -> Result<AST2> {
        let expect = ArgSpec::rest(1, 0);
        let err = |n| {
            let src = &src;
            move || { error!(ArgError, expect, got_num: n).src(src.clone()) }
        };
        let mut it = args.iter();
        let arglist = self.arg_parse(it.next().ok_or_else(err(0))?, src.clone())?;
        let body: Result<_> = it.map(|a| self.dig(a, src.clone())).collect();
        Ok(AST2 { src, kind: M::Lambda(arglist, body?) })
    }

    fn bt_define(&self, args: PV, src: Source) -> Result<AST2> {
        let expect = ArgSpec::rest(1, 1);
        let err = |n| {
            let src = &src;
            move || { error!(ArgError, expect, got_num: n).src(src.clone()) }
        };
        let mut it = args.iter();
        let lhs = it.next().ok_or_else(err(0))?;
        if let PV::Sym(name) = lhs {
            let init = Box::new(self.dig(it.next().ok_or_else(err(1))?, src.clone())?);
            let extra = it.count() as u32;
            if extra > 0 {
                Err(error!(ArgError, expect: ArgSpec::normal(2), got_num: extra + 2))
            } else {
                Ok(AST2 { kind: M::Defvar(name, init), src })
            }
        } else if lhs.is_list() {
            let body: Result<_> = it.map(|v| self.dig(v, src.clone())).collect();
            let mut it = lhs.iter();
            let name = it.next().ok_or_else(|| error!(ArgError,
                                                      expect: ArgSpec::rest(1, 0),
                                                      got_num: 0)
                                            .op(Builtin::ArgList.sym()))?;
            let name = name.sym()
                           .ok_or_else(|| error!(TypeError,
                                                 expect: Builtin::Symbol.sym(),
                                                 got: name.type_of())
                                       .argn(1).op(Builtin::ArgList.sym()))?;
            let arglist = self.arg_parse(it.into(), src.clone())?;
            Ok(AST2 { kind: M::Defun(name, arglist, body?),
                      src })
        } else {
            Err(error!(TypeNError,
                       expect: vec![Builtin::Symbol.sym(),
                                    Builtin::ArgList.sym()],
                       got: lhs.type_of()).argn(1))
        }
    }

    fn bt_next(&self, args: PV, src: Source) -> Result<AST2> {
        let e = |e: Error| e.op(sym![Next]).src(src.clone());
        let mut it = args.iter_src(self.mem, src.clone());
        if let Some((arg, src)) = it.next() {
            let extra = it.count() as u32;
            if extra > 0 {
                return Err(error!(ArgError,
                                  expect: ArgSpec::opt(0, 1),
                                  got_num: 1+extra));
            }
            Ok(M::NextIter(Box::new(self.dig(arg.car().map_err(e)?,
                                             src.clone())?)).ast(src))
        } else {
            Ok(M::Next.ast(src))
        }
    }

    fn quasi(&self, args: PV, src: Source) -> Result<AST2> {
        if args.is_atom() {
            return Ok(AST2 { src, kind: M::Atom(args) })
        }

        let root_src = src;
        let mut li = vec![];
        for (item, src) in args.iter_src(self.mem, root_src.clone()) {
            li.push(match item {
                ConsItem::Car(x) => match x.bt_op() {
                    Some(Builtin::Unquote) =>
                        AST2 { src: src.clone(),
                               kind: M::List(vec![
                                   self.dig(x.cdr().unwrap().car().expect("car"),
                                            src)? ]) },
                    Some(Builtin::USplice) =>
                        self.dig(x.cdr().unwrap().car().expect("car"), src)?,
                    _ => AST2 { kind: M::List(vec![self.quasi(x, src.clone())?]),
                                src },
                },
                ConsItem::Cdr(x) => self.quasi(x, src)?,
            })
        }

        if li.len() == 1 {
            return Ok(li.pop().unwrap());
        }
        Ok(AST2 { kind: M::Append(li), src: root_src })
    }

    fn bapp(&self, bt: Builtin, args: PV, src: Source) -> Result<AST2> {
        match bt {
            Builtin::Not => self.wrap_one_arg(M::Not, args, src),
            Builtin::And => self.wrap_any_args(M::And, args, src),
            Builtin::Or => self.wrap_any_args(M::Or, args, src),
            Builtin::Add => self.wrap_any_args(M::Add, args, src),
            Builtin::Sub => self.wrap_any_args(M::Sub, args, src),
            Builtin::Mul => self.wrap_any_args(M::Mul, args, src),
            Builtin::Div => self.wrap_any_args(M::Div, args, src),
            Builtin::Progn => self.wrap_any_args(M::Progn, args, src),
            Builtin::Loop => self.wrap_any_args(M::Loop, args, src),
            Builtin::Eq => self.chain_cmp_op(M::Eq, args, src),
            Builtin::Eqp => self.chain_cmp_op(M::Eqp, args, src),
            Builtin::Gt => self.chain_cmp_op(M::Gt, args, src),
            Builtin::Gte => self.chain_cmp_op(M::Gte, args, src),
            Builtin::Lt => self.chain_cmp_op(M::Lt, args, src),
            Builtin::Lte => self.chain_cmp_op(M::Lte, args, src),
            Builtin::If => self.bt_if(args, src),
            Builtin::Define => self.bt_define(args, src),
            Builtin::Set => self.bt_set(args, src),
            Builtin::Lambda => self.bt_lambda(args, src),
            Builtin::Quote => Ok(AST2 { src,
                                        kind: M::Atom(args.car().expect("car")) }),
            Builtin::Quasi => self.quasi(args.car().expect("car"), src),
            Builtin::Break => self.wrap_maybe_arg(M::Break, args, src),
            Builtin::Car => self.wrap_one_arg(M::Car, args, src),
            Builtin::Cdr => self.wrap_one_arg(M::Cdr, args, src),
            Builtin::Pop => self.wrap_one_arg(M::Pop, args, src),
            Builtin::CallCC => self.wrap_one_arg(M::CallCC, args, src),
            Builtin::Cons => self.wrap_two_args(M::Cons, args, src),
            Builtin::List => self.wrap_any_args(M::List, args, src),
            Builtin::Append => self.wrap_any_args(M::Append, args, src),
            Builtin::Vector => self.wrap_any_args(M::Vector, args, src),
            Builtin::Push => self.wrap_two_args(M::Push, args, src),
            Builtin::Get => self.wrap_two_args(M::Get, args, src),
            Builtin::Throw => self.wrap_one_arg(M::Throw, args, src),
            Builtin::Next => self.bt_next(args, src),
            _ => self.sapp(bt.sym(), args, src),
        }.map_err(|e| e.fallback(Meta::Op(OpName::OpSym(bt.sym()))))
    }

    fn sapp(&self, op: SymID, args: PV, src: Source) -> Result<AST2> {
        self.wrap_any_args(|a| M::SymApp(op, a), args, src)
    }

    fn lambda_app(&self,
                  ArgList2(spec, syms): ArgList2,
                  body: Progn, args: PV, src: Source) -> Result<AST2>
    {
        let orig_src = src.clone();
        let mut binds = vec![];
        let mut it = args.iter_src(self.mem, src);
        let mut argn = 0;
        while let Some((init, src)) = it.next() {
            let (sym, _) = syms[argn];
            argn += 1;
            if argn > spec.nopt() {
                if !spec.rest {
                    return Err(error!(ArgError,
                                      expect: spec,
                                      got_num: (argn + it.count()) as u32)
                               .op(Builtin::Apply.sym())
                               .src(src)
                               .see_also("lambda", orig_src))
                }
                let rest = iter::once(self.dig(init.car()?, src)).chain(
                    it.map(|(v, src)| self.dig(v.car()?, src))
                ).collect::<Result<Vec<_>>>()?;
                let (sym, src) = syms.last().cloned().unwrap();
                binds.push(VarDecl(sym, src.clone(), list(rest, src)));
                return Ok(AST2 { src: orig_src, kind: M::Let(binds, body) });
            }
            let init = Box::new(init.car().and_then(|v| self.dig(v, src.clone()))?);
            binds.push(VarDecl(sym, src.clone(), init));
        }
        if argn < spec.nargs() {
            let (sym, src) = syms[argn].clone();
            return Err(error!(ArgError,
                              expect: spec,
                              got_num: argn as u32)
                       .src(orig_src)
                       .see_also_sym(sym, src)
                       .op(Builtin::Apply.sym()));
        }
        for (sym, src) in syms.iter().cloned() {
            binds.push(VarDecl(sym, src.clone(), nil(src)))
        }
        if spec.rest {
            let (sym, src) = syms.last().cloned().unwrap();
            binds.push(VarDecl(sym, src.clone(), nil(src)))
        }
        Ok(AST2 { src: orig_src, kind: M::Let(binds, body) })
    }

    fn gapp(&self, op: PV, args: PV, src: Source) -> Result<AST2> {
        let op = self.dig(op, src.clone())?;
        if let M::Lambda(syms, body) = op.kind {
            self.lambda_app(syms, body, args, src)
        } else {
            self.wrap_any_args(|a| M::App(Box::new(op), a), args, src)
        }
    }

    fn cons(&self, Cons { car, cdr }: Cons, src: Source) -> Result<AST2> {
        if let PV::Sym(op) = car {
            if let Some(bt) = Builtin::from_sym(op) {
                self.bapp(bt, cdr, src)
            } else {
                self.sapp(op, cdr, src)
            }
        } else {
            self.gapp(car, cdr, src)
        }
    }

    fn dig(&self, v: PV, src: Source) -> Result<AST2> {
        match v {
            PV::Ref(p) => match unsafe {(*p).match_ref()} {
                NkRef::Cons(cell) => {
                    let src = self.mem.get_tag(p).cloned().unwrap_or(src);
                    self.cons(*cell, src)
                },
                _ => Ok(AST2 { src, kind: v.into() })
            }
            PV::Sym(var) => Ok(AST2 { src, kind: M::Var(var) }),
            _ => Ok(AST2 { src, kind: v.into() })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder() {
        let mut lisb = ListBuilder::new();
        for i in 0..10000 {
            lisb.push(Value::new(ValueKind::Int(i), Source::none()));
        }
        let li = lisb.get();
        for (u, v) in li.iter().enumerate() {
            if let Value { kind: ValueKind::Int(v), .. } = v {
                assert_eq!(u as i64, *v);
            } else {
                panic!("Not an integer");
            }
        }
    }
}
