//! Abstract Syntax Tree Tools

use crate::fmt::LispFmt;
use crate::nkgc::Arena;
use crate::nkgc::Cons;
use crate::nkgc::ConsItem;
use crate::nkgc::PV;
use crate::nkgc::Quasi;
use crate::nkgc::SymID;
use crate::error::*;
use crate::nuke::NkRef;
use crate::nuke::to_fissile_ref;
use crate::r8vm::ArgSpec;
use crate::builtins::Builtin;
use crate::nuke::cast_err;
use std::fmt;
use std::fmt::Display;
use std::iter;

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
    VecSet(Prog, Prog, Prog),
    Defun(SymID, ArgList2, Progn),
    Let(Vec<VarDecl>, Progn),
    Loop(Progn),
    Break(Option<Prog>),
    TailCall(Progn),
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
    // Bt(Builtin, Progn),
    Bt1(Builtin, Prog),
    Bt2(Builtin, Prog, Prog),
    Pop(Prog),
    CallCC(Prog),
}

#[derive(Debug)]
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

    pub fn binary(&self) -> Option<(M2, (&Source, &Source))> {
        let (m2, s0, s1) = match self {
            M::Add(a) if a.len() == 2 => (M2::Add(&a[0].kind, &a[1].kind), &a[0].src, &a[1].src),
            M::Sub(a) if a.len() == 2 => (M2::Sub(&a[0].kind, &a[1].kind), &a[0].src, &a[1].src),
            M::Mul(a) if a.len() == 2 => (M2::Mul(&a[0].kind, &a[1].kind), &a[0].src, &a[1].src),
            M::Div(a) if a.len() == 2 => (M2::Div(&a[0].kind, &a[1].kind), &a[0].src, &a[1].src),
            _ => return None
        };
        Some((m2, (s0, s1)))
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
                write!(f, ")")?;
            }};
        }
        match self {
            M::Bt1(op, arg) => write!(f, "({op:?} {arg})")?,
            M::Bt2(op, a0, a1) => write!(f, "({op:?} {a0} {a1})")?,
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
            M::Defvar(name, init) => write!(f, "(defvar {name} {init})")?,
            M::Set(name, init) => write!(f, "(set {name} {init})")?,
            M::VecSet(name, idx, init) => write!(f, "(set (get {name} {idx}) {init})")?,
            M::Defun(name, ArgList2(_, args), progn) => {
                write!(f, "(define ({name}")?;
                for (arg, _) in args { write!(f, " {arg}")?; }
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
            M::Var(var) => write!(f, "{var}")?,
            M::TailCall(xs) => vop!("tail", xs),
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

    #[allow(dead_code)]
    pub fn sym(sym: SymID, src: Source) -> AST2 {
        AST2 { src, kind: M::Atom(PV::Sym(sym)) }
    }

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

pub trait Visitable {
    fn visit(&mut self, visitor: &mut dyn Visitor) -> Result<()>;
}

impl Visitable for AST2 {
    fn visit(&mut self, visitor: &mut dyn Visitor) -> Result<()> {
        macro_rules! visit {
            ($($arg:expr),*) => {{
                $(visitor.visit(&mut *$arg)?;)*
            }};
        }
        macro_rules! vvisit {
            ($arg:expr) => {{
                for sub in $arg.iter_mut() { visitor.visit(sub)? }
            }};
        }
        match self.kind {
            M::Bt1(_, ref mut x) => visit!(x),
            M::Bt2(_, ref mut x, ref mut y) => visit!(x, y),
            M::VecSet(ref mut x, ref mut y, ref mut z) => visit!(x, y, z),
            M::If(ref mut a, None, None) => visit!(a),
            M::If(ref mut a, None, Some(ref mut c)) => visit!(a, c),
            M::If(ref mut a, Some(ref mut b), None) => visit!(a, b),
            M::If(ref mut a, Some(ref mut b), Some(ref mut c)) => visit!(a, b, c),
            M::Atom(_a) => (),
            M::Progn(ref mut prog) => vvisit!(prog),
            M::SymApp(_, ref mut prog) => vvisit!(prog),
            M::App(ref mut prog, ref mut progn) => { visit!(prog); vvisit!(progn) },
            M::Lambda(_, ref mut progn) => vvisit!(progn),
            M::Defvar(_, ref mut init) => visit!(init),
            M::Set(_, ref mut init) => visit!(init),
            M::Defun(_, _, ref mut progn) => vvisit!(progn),
            M::Let(ref mut vars, ref mut progn) => {
                for sub in vars.iter_mut().map(|VarDecl(_, _, init)| init) {
                    visitor.visit(sub)?;
                }
                vvisit!(progn)
            },
            M::Loop(ref mut progn) => vvisit!(progn),
            M::Break(Some(ref mut init)) => visit!(init),
            M::Break(None) => (),
            M::Next => (),
            M::Throw(ref mut init) => visit!(init),
            M::Var(_) => (),
            M::Not(ref mut x) => visit!(x),
            M::And(ref mut xs) => vvisit!(xs),
            M::Or(ref mut xs) => vvisit!(xs),
            M::Gt(ref mut x, ref mut y) => visit!(x, y),
            M::Gte(ref mut x, ref mut y) => visit!(x, y),
            M::Lt(ref mut x, ref mut y) => visit!(x, y),
            M::Lte(ref mut x, ref mut y) => visit!(x, y),
            M::Eq(ref mut x, ref mut y) => visit!(x, y),
            M::Eqp(ref mut x, ref mut y) => visit!(x, y),
            M::Add(ref mut xs) => vvisit!(xs),
            M::Sub(ref mut xs) => vvisit!(xs),
            M::Mul(ref mut xs) => vvisit!(xs),
            M::Div(ref mut xs) => vvisit!(xs),
            M::NextIter(ref mut x) => visit!(x),
            M::Car(ref mut x) => visit!(x),
            M::Cdr(ref mut x) => visit!(x),
            M::Cons(ref mut x, ref mut y) => visit!(x, y),
            M::List(ref mut xs) => vvisit!(xs),
            M::Append(ref mut xs) => vvisit!(xs),
            M::Vector(ref mut xs) => vvisit!(xs),
            M::Push(ref mut x, ref mut y) => visit!(x, y),
            M::Get(ref mut x, ref mut y) => visit!(x, y),
            M::Pop(ref mut x) => visit!(x),
            M::CallCC(ref mut x) => visit!(x),
            M::TailCall(ref mut xs) => vvisit!(xs),
        }
        Ok(())
    }
}

impl Visitable for Vec<AST2> {
    fn visit(&mut self, visitor: &mut dyn Visitor) -> Result<()> {
        for x in self.iter_mut() {
            visitor.visit(x)?;
        }
        Ok(())
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
                            None if had_opt => return Err(ErrorKind::SyntaxErrorMsg {
                                msg: "Normal argument follows &?".to_string()
                            }.into()),
                            None | Some(_) => spec.nargs += 1,
                        }
                        syms.push((sym, src));
                    }
                }
            } else {
                return Err(ErrorKind::SyntaxErrorMsg {
                    msg: format!("Did not expect: {}", arg),
                }.into());
            }
        }

        if it.next().is_some() {
            return Err(ErrorKind::SyntaxErrorMsg {
                msg: "Additional argument follows &rest".to_string(),
            }.into());
        }

        Ok(ArgList2(spec, syms))
    }

    pub fn to_ast(&self, v: PV, src: Source) -> Result<AST2> {
        self.cav(v, src)
    }

    fn cav(&self, v: PV, src: Source) -> Result<AST2> {
        let src = if let PV::Ref(p) = v {
            self.mem.get_tag(p).cloned().unwrap_or(src)
        } else {
            src
        };
        self.dig(v, src)
    }

    fn wrap_one_arg(&self, wrap: fn(Box<AST2>) -> M, args: PV, src: Source) -> Result<AST2>
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

    fn wrap_any_args_gen<F>(&self, wrap: F, args: PV, src: Source) -> Result<AST2>
        where F: FnOnce(Vec<AST2>) -> M
    {
        let args: Result<_> = args.into_iter().map(|a| self.dig(a, src.clone()))
                                              .collect();
        Ok(AST2 {
            kind: wrap(args?),
            src,
        })
    }

    fn wrap_any_args(&self, wrap: fn(Vec<AST2>) -> M, args: PV, src: Source) -> Result<AST2>
    {
        let args: Result<_> = args.into_iter().map(|a| self.dig(a, src.clone()))
                                              .collect();
        Ok(AST2 {
            kind: wrap(args?),
            src,
        })
    }

    fn chain_cmp_op(&self, cmp: fn(Box<AST2>, Box<AST2>) -> M, args: PV, src: Source) -> Result<AST2>
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

    fn wrap_two_args(&self, wrap: fn(Box<AST2>, Box<AST2>) -> M, args: PV, src: Source) -> Result<AST2>
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
        let pat = it.next().ok_or_else(err(0))?;
        let name = match pat {
            PV::Sym(name) => name,
            PV::Ref(p) => {
                let Cons { car, cdr } = unsafe { *cast_err::<Cons>(p)? };
                match car.sym().ok().and_then(Builtin::from_sym) {
                    Some(Builtin::Get) => {
                        let (vec, idx) = self.two_args(cdr, src.clone()).map_err(|e| e.bop(Builtin::Get))?;
                        // TODO: Unify this code path with the sym-set one
                        let init = Box::new(
                            self.dig(it.next().ok_or_else(err(1))?, src.clone())?
                        );
                        return Ok(AST2 {
                            kind: M::VecSet(vec, idx, init),
                            src
                        })
                    }
                    _ => bail!((UnknownSetPattern { pat: format!("(set {pat} ...)") })
                               .src(self.mem.get_tag(p).unwrap_or(&src).clone())
                               .argn(1))
                }
            }
            e => bail!((TypeError { expect: Builtin::Symbol, got: e.bt_type_of() })
                       .argn(1).src(src.clone()))
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
                                            .bop(Builtin::ArgList))?;
            let name = name.sym().map_err(|e| e.argn(1).bop(Builtin::ArgList))?;
            let arglist = self.arg_parse(it.into(), src.clone())?;
            Ok(AST2 { kind: M::Defun(name, arglist, body?),
                      src })
        } else {
            Err(error!(TypeNError,
                       expect: vec![Builtin::Symbol,
                                    Builtin::ArgList],
                       got: lhs.bt_type_of()).argn(1))
        }
    }

    fn bt_next(&self, args: PV, src: Source) -> Result<AST2> {
        let e = |e: Error| e.bop(Builtin::Next).src(src.clone());
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
        match args.quasi() {
            Some(_) => (),
            _ if args.is_atom() => return Ok(AST2 { src, kind: M::Atom(args) }),
            _ => (),
        }
        let root_src = src;
        let mut li = vec![];
        for (item, src) in args.iter_src(self.mem, root_src.clone()) {
            li.push(match item {
                ConsItem::Car(x) => match x.quasi() {
                    Some(Quasi::USplice(arg)) => self.dig(arg, src)?,
                    Some(Quasi::Unquote(arg)) =>
                        AST2 { kind: M::List(vec![self.dig(arg, src.clone())?]),
                               src },
                    None =>
                        AST2 { kind: M::List(vec![self.quasi(x, src.clone())?]),
                               src }
                }
                ConsItem::Cdr(x) => match x.quasi() {
                    Some(Quasi::USplice(_)) => bail!(SyntaxError(SyntaxErrorKind::SpliceAfterDot)),
                    Some(Quasi::Unquote(arg)) => self.dig(arg, src.clone())?,
                    None => self.quasi(x, src.clone())?,
                }
            })
        }

        if li.len() == 1 {
            return Ok(li.pop().unwrap());
        }
        Ok(AST2 { kind: M::Append(li), src: root_src })
    }

    fn quote(&self, args: PV, src: Source) -> Result<AST2> {
        if args.is_atom() { return Ok(AST2 { src, kind: M::Atom(args) }) }
        let root_src = src;
        let mut li = vec![];
        for (item, src) in args.iter_src(self.mem, root_src.clone()) {
            li.push(match item {
                ConsItem::Car(x) => {
                    AST2 { kind: M::List(vec![self.quote(x, src.clone())?]),
                           src }
                }
                ConsItem::Cdr(x) => self.quote(x, src.clone())?,
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
            Builtin::Quote => self.quote(args.car().expect("car"), src),
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
            Builtin::Len => self.wrap_one_arg(|a| M::Bt1(Builtin::Len, a), args, src),
            Builtin::Apply =>
                self.wrap_two_args(|a0, a1| M::Bt2(Builtin::Apply, a0, a1), args, src),
            Builtin::LoopWithEpilogue =>
                self.wrap_two_args(|a0, a1| M::Bt2(Builtin::LoopWithEpilogue, a0, a1), args, src),
            Builtin::Next => self.bt_next(args, src),
            _ => self.sapp(bt.sym_id(), args, src),
        }.map_err(|e| e.fallback(Meta::Op(OpName::OpBt(bt))))
    }

    fn sapp(&self, op: SymID, args: PV, src: Source) -> Result<AST2> {
        self.wrap_any_args_gen(|a| M::SymApp(op, a), args, src)
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
                               .bop(Builtin::Apply)
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
                       .bop(Builtin::Apply));
        }
        // for (sym, src) in syms.iter().cloned() {
        //     binds.push(VarDecl(sym, src.clone(), nil(src)))
        // }
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
            self.wrap_any_args_gen(|a| M::App(Box::new(op), a), args, src)
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
            PV::Ref(p) => match to_fissile_ref(p) {
                NkRef::Cons(cell) => {
                    let src = self.mem.get_tag(p).cloned().unwrap_or_else(|| src);
                    self.cons(unsafe { *cell }, src)
                },
                _ => Ok(AST2 { src, kind: v.into() })
            }
            PV::Sym(n) if n.as_ref().starts_with(':') || n == Builtin::Nil.sym_id() => {
                Ok(AST2 { src, kind: v.into() })
            }
            PV::Sym(var) => Ok(AST2 { src, kind: M::Var(var) }),
            _ => Ok(AST2 { src, kind: v.into() })
        }
    }
}

pub struct PVSrcFmt<'a> {
    pub v: PV,
    pub mem: &'a Arena
}

impl<'a> LispFmt for PVSrcFmt<'a> {
    fn lisp_fmt(&self,
                visited: &mut crate::fmt::VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let PV::Ref(p) = self.v {
            if let NkRef::Cons(cns) = to_fissile_ref(p) {
                write!(f, "(cons ", )?;
                if let Some(mut src) = self.mem.get_tag(p).cloned() {
                    src.file = None;
                    write!(f, "{src} ")?;
                } else {
                    write!(f, "[] ")?;
                }
                unsafe {
                    PVSrcFmt { v: (*cns).car, mem: self.mem }.lisp_fmt(visited, f)?;
                    write!(f, " ")?;
                    PVSrcFmt { v: (*cns).cdr, mem: self.mem }.lisp_fmt(visited, f)?;
                }
                write!(f, ")")?;
                return Ok(())
            }
        }
        self.v.lisp_fmt(visited, f)
    }
}

pub trait Visitor {
    fn visit(&mut self, elem: &mut AST2) -> Result<()>;
}

pub struct PrinterVisitor;

impl Visitor for PrinterVisitor {
    fn visit(&mut self, elem: &mut AST2) -> Result<()> {
        println!("{elem}");
        elem.visit(self)
    }
}
