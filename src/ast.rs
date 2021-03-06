//! Abstract Syntax Tree Tools

use crate::nkgc::SymID;
use crate::error::*;
use crate::tok::*;
use crate::perr::*;
use crate::sexpr_parse::string_parse;
use crate::r8vm::{R8VM, ArgInt, ArgSpec};
use crate::compile::Builtin;
use crate::compile::arg_parse;
use crate::sym_db::{SymDB, SYM_DB};
use std::fmt;
use std::ptr;

#[derive(Clone, Debug, PartialEq)]
pub enum ValueKind {
    Int(i64),
    Real(f32),
    String(String),
    Symbol(SymID),
    Cons(Box<Value>, Box<Value>),
    Bool(bool),
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
        Cons(_, _) => {
            write!(f, "(")?;
            let mut head = val;
            loop {
                match &head.kind {
                    Cons(car, cdr) => {
                        fmt_value(&*car, f, db)?;
                        if cdr.is_nil() {
                            break;
                        }
                        write!(f, " ")?;
                        head = &*cdr;
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt_value(self, f, &SYM_DB)
    }
}

pub struct LetBinding<'a>(pub SymID,
                          pub &'a Value,
                          pub &'a Source);
pub struct Let<'a>(pub Vec<LetBinding<'a>>,
                   pub &'a Value);

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

pub struct DefineVar<'a>(pub SymID,
                         pub &'a Value);
pub struct DefineFunc<'a>(pub SymID,
                          pub ArgList,
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
        }
    }

    /**
     * Applications like `((lambda (x) (+ x 2)) 2)` are compiled just like
     * `(let ((x 2)) (+ x 2))`.
     */
    pub fn bt_lambda_bind(&self) -> Option<Result<Let, Error>> {
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

    pub fn bt_let(&self) -> Result<Let, Error> {
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
                                Ok(LetBinding(*sym, *val, src)),
                            _ => err()
                        }
                    }).collect::<Result<Vec<_>, Error>>()?;
            Ok(Let(pairs, it.head()))
        } else {
            err_src!(self.src.clone(),
                     ArgError,
                     expect: ArgSpec::rest(1, 0),
                     got_num: 0,
                     op: Builtin::Let.sym())
        }
    }

    pub fn bt_define(&self) -> Result<Define, Error> {
        let op = Builtin::Define.sym();
        let expect = ArgSpec::rest(1, 1);
        let mut it = self.args();
        let src = self.src.clone();
        match it.next() {
            Some(Value { kind: ValueKind::Symbol(var), .. }) => {
                let init = it.next().ok_or_else(|| {
                    error_src!(src, ArgError, op, expect, got_num: 1)
                })?;
                Ok(Define::Var(*var, init))
            }
            Some(fn_def @ Value { kind: ValueKind::Cons(..), .. }) => {
                let mut def_it = fn_def.iter();
                let name = match def_it.next() {
                    Some(Value { kind: ValueKind::Symbol(name), .. }) =>
                        Ok(name),
                    Some(x) => err_src!(fn_def.src.clone(), TypeError, op,
                                        expect: Builtin::Symbol.sym(),
                                        got: x.type_of(),
                                        argn: 1),
                    _ => unreachable!(),
                }?;
                let (syms, spec) = arg_parse(def_it.head())?;
                Ok(Define::Func(*name, ArgList(spec, syms), it.head()))
            }
            None => err_src!(src, ArgError, op, expect, got_num: 0),
            Some(x) => err_src!(src, TypeError, op,
                                expect: Builtin::Symbol.sym(),
                                got: x.type_of(),
                                argn: 1),
        }
    }

    pub fn bt_get(&self) -> Option<Result<Get, Error>> {
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

    pub fn bt_lambda(&self) -> Result<Lambda, Error> {
        let mut it = self.args();
        let (args, spec) = if let Some(args) = it.next() {
            arg_parse(args)?
        } else {
            return err_src!(self.src.clone(), ArgError,
                            expect: ArgSpec::rest(1, 0),
                            got_num: 0,
                            op: Builtin::Lambda.sym())
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

    pub fn from_token(vm: &mut R8VM, tok: &Token) -> PResult<Value> {
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
        Ok(Value { kind, src: Source::new(tok.line, tok.col) })
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
            node = if let ValueKind::Cons(ref mut cdar, _) = (*cdr).kind {
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
        if let Some(sym) = self.op() {
            Some((sym, self.args()))
        } else {
            None
        }
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
