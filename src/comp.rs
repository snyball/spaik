//! SPAIK v2 Compiler

use std::collections::hash_map;
use std::{iter, mem};
use std::sync::atomic::{Ordering, AtomicUsize};

use chasm::LblMap;

use crate::utils::{HSet, HMap};
use crate::nkgc::{PV, SymID, Int};
use crate::r8vm::{R8VM, ArgSpec, r8c, Func};
use crate::chasm::{ChOp, ChASM, Lbl, self, Arg};
use crate::error::Source;
use crate::ast::{AST2, M, Prog, Progn, M2, ArgList2, VarDecl, Visitor, Visitable};
use crate::r8vm::r8c::{OpName::*, Op as R8C};
use crate::builtins::*;
use crate::error::Result;

static LAMBDA_COUNT: AtomicUsize = AtomicUsize::new(0);
static MODULE_COUNT: AtomicUsize = AtomicUsize::new(0);
static DEFVAR_COUNT: AtomicUsize = AtomicUsize::new(0);

macro_rules! def_macros {
    ($d:tt, $ret:expr, $self:expr) => {
        #[allow(unused_macros)]
        macro_rules! asm {
            ($d ($d args:tt)*) => {{ $self.unit().op(chasm!($d ($d args)*)); }};
        }

        #[allow(unused_macros)]
        macro_rules! opcall_mut {
            ($d op:ident $d ($d arg:expr),*) => {{
                $d ($self.push($d arg)?;)*
                asm!($d op);
                if !$ret {
                    asm!(POP 1);
                }
                $self.env_pop(count_args!($d($d arg),*))?;
            }};
        }
    };
}

pub type SourceList = Vec<(usize, Source)>;

type VarIdx = u32;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum BoundVar {
    Local(VarIdx),
    Env(VarIdx),
}

#[derive(Default, Debug)]
struct Env {
    name: Option<SymID>,
    vars: Vec<SymID>,
    statics: HMap<SymID, usize>,
}

// FIXME: Statics and locals need to be merged somehow, right
//        now a local (let) always takes precedence over a static
//        variable (intr::define-static)
impl Env {
    pub fn new(name: Option<SymID>, args: Vec<SymID>) -> Env {
        let mut env = Env {
            name,
            vars: args,
            statics: Default::default()
        };
        env.defvar(Builtin::IP.sym_id());
        env.defvar(Builtin::Frame.sym_id());
        env
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn none(name: Option<SymID>) -> Env {
        Env { vars: vec![], statics: Default::default(), name }
    }

    pub fn defvar(&mut self, var: SymID) {
        self.vars.push(var);
    }

    pub fn anon(&mut self) -> usize {
        let pos = self.vars.len();
        self.vars.push(Builtin::Epsilon.sym_id());
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


#[derive(Debug)]
pub enum Sym {
    Id(SymID),
    Str(String),
}

/**
 * Compile Value into R8C code.
 */
#[derive(Debug)]
pub struct R8Compiler {
    labels: LblMap,
    code: Vec<R8C>,
    units: Vec<ChASM<R8C>>,
    srctbl: SourceList,
    estack: Vec<Env>,
    loops: Vec<LoopCtx>,
    fn_ctxs: Vec<FnCtx>,
    const_offset: usize,
    consts: Vec<PV>,
    code_offset: usize,
    new_fns: Vec<(Sym, ArgSpec, Vec<SymID>, usize, usize)>,
    new_envs: Vec<(SymID, usize, usize)>,
    env: HMap<SymID, usize>,
    fns: HMap<SymID, Func>,
    unlinked_fns: HMap<SymID, Vec<usize>>,
    #[allow(dead_code)]
    debug_mode: bool,
}

#[derive(Debug, Clone, Copy)]
struct FnCtx {
    start: Lbl,
}

#[derive(Debug, Clone, Copy)]
struct LoopCtx {
    start: Lbl,
    epilogue: Option<Lbl>,
    end: Lbl,
    ret: bool,
    height: usize,
}

type VarSet = HSet<(SymID, BoundVar)>;
type FnSet = HMap<SymID, Func>;

struct ClzScoper<'a, 'b, 'c> {
    env: Env,
    outside: &'a Env,
    fns: &'b FnSet,
    lowered: VarSet,
    globals: &'c HMap<SymID, usize>,
}

impl Visitor for ClzScoper<'_, '_, '_> {
    fn visit(&mut self, elem: &mut AST2) -> Result<()> {
        match elem.kind {
            M::SymApp(op, _) => if let Some(var) = self.outside.get_idx(op) {
                self.lowered.insert((op, BoundVar::Local(var)));
            }
            M::Let(ref vars, _) => {
                let len = vars.len();
                vars.iter().for_each(|VarDecl(var, _, _)| self.env.defvar(*var));
                elem.visit(self)?;
                self.env.pop(len);
                return Ok(());
            }
            M::Lambda(ArgList2(_, ref vars), _) => {
                let len = vars.len();
                vars.iter().for_each(|(var, _)| self.env.defvar(*var));
                elem.visit(self)?;
                self.env.pop(len);
                return Ok(());
            }
            M::Var(var) => {
                if self.env.get_idx(var).is_some() {
                } else if let Some(bound) = self.outside.get_idx(var) {
                    self.lowered.insert((var, BoundVar::Local(bound)));
                } else if self.globals.get(&var).is_some() {
                } else if var != Builtin::Nil.sym_id() && !self.fns.contains_key(&var) {
                    return err_src!(elem.src.clone(), UndefinedVariable, var: var.into());
                }
            }
            _ => ()
        }
        elem.visit(self)
    }
}

impl ClzScoper<'_, '_, '_> {
    pub fn scope<'a, 'b>(args: Vec<SymID>,
                         globals: &HMap<SymID, usize>,
                         outside: &Env,
                         fns: &'b FnSet,
                         body: impl Iterator<Item = &'a mut AST2>) -> Result<VarSet> {
        let mut scoper = ClzScoper {
            lowered: Default::default(),
            env: Env::new(None, args),
            fns,
            outside,
            globals
        };
        for part in body {
            scoper.visit(part)?;
        }
        Ok(scoper.lowered)
    }
}

fn add_unlinked(ufns: &mut HMap<SymID, Vec<usize>>, name: SymID, pos: usize) {
    match ufns.entry(name) {
        hash_map::Entry::Occupied(mut e) => e.get_mut().push(pos),
        hash_map::Entry::Vacant(e) => {e.insert(vec![pos]);}
    }

}

impl R8Compiler {
    pub fn new(vm: &R8VM) -> R8Compiler {
        let mut cc = R8Compiler {
            const_offset: 0,
            debug_mode: vm.get_debug_mode(),
            fn_ctxs: Default::default(),
            new_fns: Default::default(),
            estack: Default::default(),
            labels: Default::default(),
            consts: Default::default(),
            loops: Default::default(),
            srctbl: Default::default(),
            code: Default::default(),
            units: Default::default(),
            new_envs: Default::default(),
            env: vm.globals.clone(),
            unlinked_fns: Default::default(),
            fns: {
                let mut map: HMap<SymID, Func> = Default::default();
                for (sym, funk) in vm.funcs.iter() {
                    map.insert(*sym, *funk);
                }
                map
            },
            code_offset: 0,
        };
        cc.begin_unit();
        let none: Option<SymID> = None;
        cc.enter_fn(None, none.into_iter(), ArgSpec::none());
        cc.set_offsets(vm);
        cc
    }

    // FIXME: This is SLOW and has to be REMOVED removed
    pub fn update_globals(&mut self, vm: &R8VM) {
        if vm.globals.len() != self.env.len() {
            for (k, v) in vm.globals.iter() {
                self.env.insert(*k, *v);
            }
        }
    }

    pub fn unit(&mut self) -> &mut ChASM<R8C> {
        self.units.last_mut().expect("No unit to save asm to")
    }

    pub fn end_unit(&mut self) -> Result<usize> {
        let len = self.code.len();
        self.units.pop()
                  .expect("No unit to end")
                  .link_into(&mut self.code,
                             len + self.code_offset,
                             &mut self.labels)
    }

    pub fn begin_unit(&mut self) {
        self.units.push(ChASM::new())
    }

    pub fn set_source(&mut self, src: Source) {
        if src.line == 0 { return } // FIXME: This shouldn't be necessary
        match self.srctbl.last() {
            Some((_, last_src)) if *last_src == src => (),
            _ => {
                let idx = self.unit().len() + self.code_offset;
                self.srctbl.push((idx, src));
            }
        }
    }

    pub fn enter_fn(&mut self,
                    name: Option<SymID>,
                    args: impl Iterator<Item = SymID>,
                    spec: ArgSpec) {
        let mut env = Env::none(name);
        if spec.has_env() {
            env.defvar(Builtin::LambdaObject.sym_id());
        }
        for arg in args {
            env.defvar(arg);
        }
        env.defvar(Builtin::IP.sym_id());
        env.defvar(Builtin::Frame.sym_id());
        self.estack.push(env);
        let start = self.unit().label("fn-begin");
        self.unit().mark(start);
        self.fn_ctxs.push(FnCtx { start });
        if spec.is_special() {
            self.unit().op(chasm!(SAV 2));
            if spec.has_opt() {
                self.unit().op(chasm!(TOP spec.nargs));
                self.unit().op(chasm!(JV 1, spec.nopt));
                for _ in 0..spec.nopt {
                    self.unit().op(chasm!(NIL));
                }
            }
            if spec.has_body() {
                self.unit().op(chasm!(TOP spec.nargs + spec.nopt + spec.env));
                self.unit().op(chasm!(VLT));
            }
            if spec.has_env() {
                self.unit().op(chasm!(ZXP));
            }
            self.unit().op(chasm!(RST));
        }
    }

    fn leave_fn(&mut self) {
        self.unit().op(chasm!(RET));
        self.estack.pop();
        self.fn_ctxs.pop();
    }

    fn with_env<T>(&mut self, f: impl Fn(&mut Env) -> T) -> Result<T> {
        self.estack
            .last_mut()
            .map(f)
            .ok_or_else(|| "No environment".into())
    }

    #[inline]
    fn asm_op(&mut self, op: ChOp<r8c::OpName>) {
        self.unit().op(op);
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
    fn push(&mut self, code: AST2) -> Result<usize> {
        self.compile(true, code)?;
        self.with_env(|env| env.anon())
    }

    fn pushit(&mut self, args: impl Iterator<Item = AST2>) -> Result<usize> {
        let mut nargs = 0;
        for arg in args {
            nargs += 1;
            self.push(arg)?;
        }
        Ok(nargs)
    }

    fn env_pop(&mut self, n: usize) -> Result<()> {
        self.with_env(|env| env.pop(n))
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
     * Where the boolean represents whether or not the inner expression
     * has been negated.
     *
     * # Algorithm
     *
     * [Video explanation.](https://youtu.be/ohDB5gbtaEQ?t=65)
     */
    pub fn argument_clinic(mut code: AST2) -> (bool, AST2) {
        let mut flipped = false;
        while let AST2 { kind: M::Not(sub), .. } = code {
            flipped = !flipped;
            code = *sub;
        }
        (flipped, code)
    }

    fn loop_ctx(&self) -> Result<&LoopCtx> {
        self.loops
            .last()
            .ok_or(error!(OutsideContext,
                          op: Builtin::Break,
                          ctx: Builtin::Loop))
    }

    fn loop_epilogue(&self) -> Result<Lbl> {
        self.loop_ctx().map(|ctx| ctx.epilogue.unwrap_or(ctx.start))
    }

    fn loop_end(&self) -> Result<Lbl> {
        self.loop_ctx().map(|ctx| ctx.end)
    }

    fn loop_simple_jmp_to(&self, op: &M) -> Option<Result<Lbl>> {
        match (op, self.loop_ctx().map(|x| x.ret).ok()) {
            (M::Break(None), Some(false)) => Some(self.loop_end()),
            (M::Next, Some(false)) => Some(self.loop_epilogue()),
            _ => None
        }
    }

    fn bt_if(&mut self, ret: bool,
             cond: AST2, if_t: Option<AST2>, if_f: Option<AST2>
    ) -> Result<()> {
        let if_t = if_t.unwrap_or_else(|| AST2::nil(cond.src.clone()));
        let (flipped, cond) = R8Compiler::argument_clinic(cond);
        let src = cond.src.clone();
        let ((jt, jn), cond) = match cond.kind {
            M::Eq(u, v) => match (*u, *v) {
                (AST2 { kind: M::Atom(PV::Int(0)), .. }, v) |
                (v, AST2 { kind: M::Atom(PV::Int(0)), .. }) => ((JZ, JNZ), v),
                (u, v) => ((JT, JN),
                           AST2 { src, kind: M::Eq(Box::new(u), Box::new(v)) }),
            },
            _ => ((JT, JN), cond)
        };
        self.compile(true, cond)?;

        if let Some(lbl) = self.loop_simple_jmp_to(&if_t.kind) {
            if flipped {
                self.unit().op(chasm!(jn lbl?));
            } else {
                self.unit().op(chasm!(jt lbl?));
            }
            if let Some(if_false) = if_f {
                self.compile(ret, if_false)?;
            } else if ret {
                self.unit().op(chasm!(NIL));
            }
        } else {
            let end_lbl = self.unit().label("if_end");
            let if_false_lbl = self.unit().label("if_false");
            let _jmp_loc = if flipped {
                self.unit().op(chasm!(jt if_false_lbl))
            } else {
                self.unit().op(chasm!(jn if_false_lbl))
            };
            self.compile(ret, if_t)?;
            if let Some(if_false) = if_f {
                self.asm_op(chasm!(JMP end_lbl));
                self.unit().mark(if_false_lbl);
                self.compile(ret, if_false)?;
                self.unit().mark(end_lbl);
            } else if ret {
                self.asm_op(chasm!(JMP end_lbl));
                self.unit().mark(if_false_lbl);
                self.unit().op(chasm!(NIL));
                self.unit().mark(end_lbl);
            } else {
                self.unit().mark(if_false_lbl);
            }
        }
        Ok(())
    }

    fn compile_seq(&mut self,
                   ret: bool,
                   seq: impl IntoIterator<Item = AST2>
    ) -> Result<()> {
        let mut seq = seq.into_iter();
        let Some(mut last) = seq.next() else {
            if ret { self.asm_op(chasm!(NIL)) }
            return Ok(())
        };
        for nx in seq {
            self.compile(false, last)?;
            last = nx;
        }
        self.compile(ret, last)
    }

    // FIXME: This API is a bit weird.
    /// `nargs_idx` is the index in op.1 that holds the number
    /// of arguments. Used in instructions like VCALL, LIST,
    /// CLZCALL, etc.
    fn gen_call_nargs(&mut self,
                      ret: bool,
                      op: (r8c::OpName, &mut [chasm::Arg]),
                      nargs_idx: usize,
                      args: impl Iterator<Item = AST2>) -> Result<()> {
        let nargs = self.pushit(args)?;
        op.1[nargs_idx] = nargs.into();
        self.unit().add(op.0, op.1);
        self.env_pop(nargs)?;
        if !ret {
            self.asm_op(chasm!(POP 1));
        }
        Ok(())
    }

    fn asm_get_var(&mut self,
                   var: SymID,
                   src: &Source) -> Result<()> {
        match self.get_var_idx(var, src)? {
            BoundVar::Local(idx) => self.unit().op(chasm!(MOV idx)),
            BoundVar::Env(idx) => self.unit().op(chasm!(GET idx)),
        };
        Ok(())
    }

    fn get_var_idx(&mut self,
                   var: SymID,
                   src: &Source) -> Result<BoundVar> {
        if let Some(idx) = self.with_env(|env| env.get_idx(var))? {
            return Ok(BoundVar::Local(idx));
        }
        for env in self.estack.iter().rev() {
            if let Some(idx) = env.get_env_idx(var) {
                return Ok(BoundVar::Env(idx as u32))
            }
        }
        if let Some(idx) = self.env.get(&var) {
            return Ok(BoundVar::Env(*idx as u32))
        }
        err_src!(src.clone(), UndefinedVariable, var: var.into())
    }

    fn asm_set_var_idx(&mut self, idx: &BoundVar) -> Result<()> {
        match idx {
            BoundVar::Local(idx) => self.unit().op(chasm!(STR *idx)),
            BoundVar::Env(idx) => self.unit().op(chasm!(SET *idx)),
        };
        Ok(())
    }

    fn bt_sym_app(&mut self, ret: bool, src: Source, op: SymID, args: Vec<AST2>) -> Result<()> {
        if let Ok(()) = self.asm_get_var(op, &src) { // Call to closure variable
            self.with_env(|env| env.anon())?;
            let args = args.into_iter();
            self.gen_call_nargs(ret, (r8c::OpName::ZCALL, &mut [0.into()]),
                                0, args)?;
            self.env_pop(1).unwrap();
        } else if self.with_env(|e| e.name)?.map(|s| op == s).unwrap_or_default() {
            let start = self.fn_ctxs.last().unwrap().start;
            self.gen_call_nargs(ret, (r8c::OpName::CALL,
                                      &mut [Arg::AbsLbl(start), 0.into()]),
                                1, args.into_iter())?;
        } else { // Call to symbol (virtual call)
            let idx = self.new_const(PV::Sym(op));
            self.gen_call_nargs(ret, (r8c::OpName::VCALL,
                                      &mut [idx.into(), 0.into()]),
                                1, args.into_iter())?;
        }
        Ok(())
    }

    fn gapp(&mut self, ret: bool, op: AST2, args: Vec<AST2>) -> Result<()> {
        if !matches!(op.type_of(), Builtin::Unknown | Builtin::Lambda) {
            return Err(error!(TypeError,
                              expect: Builtin::Lambda,
                              got: op.type_of())
                       .src(op.src).argn(0).bop(Builtin::Apply))
        }
        self.compile(true, op)?;
        self.with_env(|env| env.anon())?; // closure
        self.gen_call_nargs(ret, (r8c::OpName::ZCALL, &mut [0.into()]),
                            0, args.into_iter())?;
        self.env_pop(1)
    }

    pub fn bt_vec_set(&mut self,
                      ret: bool,
                      _src: Source,
                      dst: AST2,
                      idx: AST2,
                      init: AST2) -> Result<()> {
        self.compile(true, init)?;
        if ret { self.unit().op(chasm!(DUP)); }
        self.compile(true, dst)?;
        self.compile(true, idx)?;
        self.unit().op(chasm!(VSET));
        Ok(())
    }

    pub fn bt_set(&mut self,
                  ret: bool,
                  src: Source,
                  dst: SymID,
                  init: AST2) -> Result<()> {
        let bound = self.get_var_idx(dst, &src)?;
        if let BoundVar::Local(idx) = bound {
            let mut inplace_op = |op, val: Int| {
                self.unit().add(op, &[idx.into(), val.into()]);
                if ret { self.asm_op(chasm!(MOV idx)) }
            };
            match init.kind.binary() {
                // Handle (set x (+ x 2)) => INC x, 2
                //        (set x (+ 1 x)) => INC x, 1
                //        (set x (- x 1)) => DEC x, 1
                //        (set x (- 1 x)) => Not special
                Some((M2::Add(M::Var(sym), M::Atom(PV::Int(num))), _)) |
                Some((M2::Add(M::Atom(PV::Int(num)), M::Var(sym)), _))
                    if *sym == dst => {
                    inplace_op(INC, *num);
                    return Ok(())
                }
                Some((M2::Sub(M::Var(sym), M::Atom(PV::Int(num))), _))
                    if *sym == dst => {
                    inplace_op(DEC, *num);
                    return Ok(())
                }
                Some((M2::Add(M::Var(u), M::Var(v)), (src_u, src_v))) => 'out: {
                    let (src, src_src) =
                        if *u == dst { (*v, src_v) }
                        else if *v == dst { (*u, src_u) }
                        else { break 'out };
                    if let BoundVar::Local(src_idx) = self.get_var_idx(src, src_src)? {
                        self.unit().op(chasm!(ADS idx, src_idx));
                        return Ok(())
                    }
                }
                Some((M2::Sub(M::Var(u), M::Var(v)), (_, src_v))) if *u == dst => {
                    if let BoundVar::Local(src_idx) = self.get_var_idx(*v, src_v)? {
                        self.unit().op(chasm!(SUS idx, src_idx));
                        return Ok(())
                    }
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

    fn lambda(&mut self,
              name: Option<SymID>,
              spec: ArgSpec,
              names: Vec<(SymID, Source)>,
              prog: impl IntoIterator<Item = AST2>) -> Result<(usize, usize)> {
        self.begin_unit();
        self.enter_fn(name, names.into_iter().map(|(s,_)| s), spec);
        self.compile_seq(true, prog)?;
        self.leave_fn();
        let pos = self.code.len() + self.code_offset;
        let sz = self.end_unit()?;
        Ok((pos, sz))
    }

    fn bt_lambda(&mut self,
                 mut spec: ArgSpec,
                 names: Vec<(SymID, Source)>,
                 mut prog: Progn,
                 _src: Source) -> Result<()> {
        let mut args: Vec<_> = names.iter().map(|(s,_)| *s).collect();
        let Some(outside) = self.estack.last() else { unimplemented!() };
        let lowered = ClzScoper::scope(args.clone(),
                                       &self.env,
                                       outside,
                                       &self.fns,
                                       prog.iter_mut())?;
        let num = LAMBDA_COUNT.fetch_add(1, Ordering::SeqCst);
        let name = format!("<λ>-{num}");
        let mut num = 0;
        for (var, bound) in lowered.iter() {
            if let BoundVar::Local(idx) = bound {
                args.push(*var);
                self.unit().op(chasm!(MOV *idx));
                num += 1;
            }
        }
        spec.env = num;
        self.begin_unit();
        self.enter_fn(None, args.iter().copied(), spec);
        for (var, bound) in lowered.iter() {
            if let BoundVar::Env(idx) = bound {
                self.with_env(|env| env.defenv(*var, *idx as usize))?;
            }
        }
        self.compile_seq(true, prog)?;
        if spec.has_env() {
            self.asm_op(chasm!(ZAV spec.sum_nargs() + 1, spec.env));
        }
        self.leave_fn();
        let pos = self.code.len() + self.code_offset;
        let sz = self.end_unit()?;
        self.unit().op(
            chasm!(ARGS spec.nargs, spec.nopt, spec.env, spec.rest as u8)
        );
        self.unit().op(chasm!(CLZ pos, num));
        self.new_fns.push((Sym::Str(name), spec, args, pos, sz));
        Ok(())
    }

    fn popa(&mut self, num: usize) {
        match self.unit().last_mut() {
            Some(ChOp { id: r8c::OpName::POPA, ref mut args }) => {
                args[1].add_mut(num as isize)
                       .expect("Invalid popa instruction");
            },
            _ => { self.unit().op(chasm!(POPA 1, num)); },
        }
    }

    fn bt_let(&mut self, ret: bool, decls: Vec<VarDecl>, prog: Progn) -> Result<()> {
        let len = decls.len();
        for VarDecl(name, _src, val) in decls.into_iter() {
            self.compile(true, *val)?;
            self.with_env(|env| env.defvar(name))?;
        }
        self.compile_seq(ret, prog)?;
        if ret {
            self.popa(len);
        } else {
            self.unit().op(chasm!(POP len));
        }
        self.env_pop(len)
    }

    fn bt_loop(&mut self,
               ret: bool,
               seq: impl IntoIterator<Item = AST2>,
               epl: Option<impl IntoIterator<Item = AST2>>) -> Result<()> {
        let start = self.unit().label("loop_start");
        let end = self.unit().label("loop_end");
        let epl_lbl = if epl.is_some() { Some(self.unit().label("epilogue")) } else { None };
        let height = self.with_env(|env| env.len())?;
        self.loops.push(LoopCtx { start, end, epilogue: epl_lbl, ret, height });
        self.unit().mark(start);
        self.compile_seq(false, seq)?;
        if let Some(epl) = epl {
            self.unit().mark(epl_lbl.unwrap());
            self.compile_seq(false, epl)?;
        }
        self.unit().op(chasm!(JMP start));
        self.unit().mark(end);
        self.loops.pop();
        Ok(())
    }

    fn bt_break(&mut self, src: Source, arg: Option<Prog>) -> Result<()> {
        let outer = self.loops
                        .last()
                        .copied()
                        .ok_or(error_src!(src, OutsideContext,
                                          op: Builtin::Break,
                                          ctx: Builtin::Loop))?;
        let LoopCtx { end, ret, height, .. } = outer;
        let dist = self.with_env(|env| env.len())? - height;
        let popa = |cc: &mut R8Compiler| if dist > 0 {
            cc.popa(dist-1);
        };
        match arg {
            Some(code) if ret => {
                self.compile(true, *code)?;
                popa(self);
            }
            None if ret => {
                self.asm_op(chasm!(NIL));
                popa(self);
            }
            _ if dist > 0 => self.asm_op(chasm!(POP dist)),
            _ => ()
        }
        self.asm_op(chasm!(JMP end));
        Ok(())
    }

    fn bt_loop_next(&mut self, src: Source) -> Result<()> {
        let outer = self.loops
                        .last()
                        .copied()
                        .ok_or(error_src!(src, OutsideContext,
                                          op: Builtin::Next,
                                          ctx: Builtin::Loop))?;
        let LoopCtx { start, epilogue, height, .. } = outer;
        let dist = self.with_env(|env| env.len())? - height;
        self.asm_op(chasm!(POP dist));
        if let Some(epl) = epilogue {
            self.asm_op(chasm!(JMP epl));
        } else {
            self.asm_op(chasm!(JMP start));
        }
        Ok(())
    }

    fn binop(&mut self,
             op: Builtin,
             src: Source,
             bop: ChOp<r8c::OpName>,
             one_arg_pre: Option<ChOp<r8c::OpName>>,
             default: Option<ChOp<r8c::OpName>>,
             args: impl IntoIterator<Item = AST2>) -> Result<()> {
        let mut it = args.into_iter().peekable();
        if let Some(fst) = it.next() {
            if let (Some(pre), true) = (one_arg_pre, it.peek().is_none()) {
                self.unit().op(pre);
                self.with_env(|env| env.anon())?;
                self.compile(true, fst)?;
                self.unit().op(bop);
            } else {
                self.push(fst)?;
                for arg in it {
                    self.compile(true, arg)?;
                    self.unit().op(bop.clone());
                }
            }
            self.env_pop(1)?;
        } else if let Some(op) = default {
            self.unit().op(op);
        } else {
            return Err(error!(ArgError,
                              expect: ArgSpec::rest(1, 0),
                              got_num: 0)
                       .src(src).bop(op))
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
    fn bt_vpush(&mut self, ret: bool, vec: AST2, val: AST2) -> Result<()> {
        self.push(val)?;
        if ret {
            self.unit().op(chasm!(DUP));
        }
        self.push(vec)?;
        self.unit().op(chasm!(VPUSH));
        self.env_pop(2)
    }

    fn bt_next(&mut self, ret: bool, arg: AST2) -> Result<()> {
        let AST2 { src, kind } = arg;
        match kind {
            M::Var(var) => {
                let bound = self.get_var_idx(var, &src)?;
                match bound {
                    BoundVar::Local(idx) => self.asm_op(chasm!(NXT idx)),
                    BoundVar::Env(idx) => {
                        self.asm_op(chasm!(GET idx));
                        let idx = self.with_env(|env| env.anon())?;
                        self.asm_op(chasm!(NXT idx));
                        self.popa(1);
                        self.env_pop(1)?;
                    }
                }
            }
            init => {
                self.compile(true, AST2 { kind: init, src })?;
                let idx = self.with_env(|env| env.anon())?;
                self.asm_op(chasm!(NXT idx));
                self.popa(1);
                self.env_pop(1)?;
            }
        };
        if !ret {
            self.asm_op(chasm!(POP 1));
        }
        Ok(())
    }

    fn bt_and(&mut self, ret: bool, args: impl IntoIterator<Item = AST2>) -> Result<()> {
        let mut it = args.into_iter().peekable();
        if it.peek().is_none() {
            if ret {
                self.unit().op(chasm!(BOOL 1));
            }
            return Ok(());
        }
        let end_l = self.unit().label("and_end");
        let and_exit = self.unit().label("and_early_exit");
        while let Some(part) = it.next() {
            let (flip, part) = R8Compiler::argument_clinic(part);
            self.compile(it.peek().is_some() || ret, part)?;
            if flip {
                self.unit().op(chasm!(JT and_exit));
            } else {
                self.unit().op(chasm!(JN and_exit));
            }
        }
        self.unit().pop();
        if ret {
            self.unit().op(chasm!(JMP end_l));
            self.unit().mark(and_exit);
            self.unit().op(chasm!(NIL));
            self.unit().mark(end_l);
        } else {
            self.unit().mark(and_exit);
        }
        Ok(())
    }

    fn bt_or(&mut self, ret: bool, args: impl IntoIterator<Item = AST2>) -> Result<()> {
        let mut it = args.into_iter().peekable();
        if it.peek().is_none() {
            if ret {
                self.unit().op(chasm!(BOOL 0));
            }
            return Ok(());
        }
        let end_l = self.unit().label("or_end");
        while let Some(part) = it.next() {
            let (flip, part) = R8Compiler::argument_clinic(part);
            self.compile(it.peek().is_some() || ret, part)?;
            if ret { self.unit().op(chasm!(DUP)); }
            if flip {
                self.unit().op(chasm!(JN end_l));
            } else {
                self.unit().op(chasm!(JT end_l));
            }
            if ret { self.unit().op(chasm!(POP 1)); }
        }
        if ret { self.unit().op(chasm!(NIL)); }
        self.unit().mark(end_l);
        Ok(())
    }

    pub fn new_const(&mut self, pv: PV) -> usize {
        let idx = self.const_offset + self.consts.len();
        self.consts.push(pv);
        idx
    }

    fn atom(&mut self, pv: PV) -> Result<()> {
        let op = match pv {
            PV::Bool(true) => chasm!(BOOL 1),
            PV::Bool(false) => chasm!(BOOL 0),
            PV::Char(c) => chasm!(CHR c as u32),
            PV::Int(i) => chasm!(INT i),
            PV::Real(r) => chasm!(FLT r.to_bits()),
            PV::Nil => chasm!(NIL),
            pv => {
                let idx = self.new_const(pv);
                if pv.bt_type_of() == Builtin::String {
                    chasm!(GET idx) // Strings are immutable, no need to clone
                } else {
                    chasm!(INS idx)
                }
            }
        };
        self.unit().op(op);
        Ok(())
    }

    fn bt_append(&mut self, ret: bool, mut xs: Vec<AST2>, src: Source) -> Result<()> {
        if xs.iter().all(|e| matches!(e.kind, M::List(..))) {
            let ast = AST2 {
                src,
                kind: M::List(xs.into_iter().flat_map(|xs| if let M::List(src) = xs.kind {
                    src.into_iter()
                } else {
                    unreachable!()
                }).collect())
            };
            self.compile(ret, ast)
        } else {
            if let Some(mut i) = xs.iter().position(|m| matches!(m.kind, M::List(..))) {
                for j in (i+1)..xs.len() {
                    match xs[j].kind {
                        M::List(..) => {
                            let (pre, post) = xs.split_at_mut(j);
                            let M::List(dst) = &mut pre[i].kind else {
                                i = j;
                                continue
                            };
                            let M::List(src) = &mut post[0].kind else { unreachable!() };
                            dst.append(src);
                        }
                        _ => i = j,
                    }
                }
                xs.retain(|s| if let M::List(xs) = &s.kind {
                    !xs.is_empty()
                } else { true });
            }
            let nargs = xs.len();
            for arg in xs.into_iter() {
                self.compile(ret, arg)?;
            }
            if ret { self.unit().op(chasm!(APN nargs)); }
            Ok(())
        }
    }

    pub fn bt1(&mut self, ret: bool, op: Builtin, arg: Box<AST2>) -> Result<()> {
        match op {
            Builtin::Len => self.opcall(ret, LEN, [arg])?,
            x => unimplemented!("{x:?}"),
        }

        Ok(())
    }

    pub fn bt2(&mut self, ret: bool, op: Builtin, a0: AST2, a1: AST2) -> Result<()> {
        def_macros!($, ret, self);

        match op {
            Builtin::Apply => opcall_mut!(APL a0, a1),
            Builtin::LoopWithEpilogue => self.bt_loop(ret,
                                                      Some(a0),
                                                      Some(Some(a1).into_iter()))?,
            x => unimplemented!("{x:?}"),
        }

        Ok(())
    }

    fn opcall<const N: usize>(&mut self, ret: bool, op: r8c::OpName, args: [Box<AST2>; N]) -> Result<()> {
        if ret {
            let len = args.len();
            for arg in args.into_iter() {
                self.push(*arg)?;
            }
            self.asm_op(ChOp::new(op, vec![]));
            self.env_pop(len)?;
        } else {
            for arg in args.into_iter() {
                self.compile(false, *arg)?;
            }
        }
        Ok(())
    }

    fn vopcall(&mut self, ret: bool, op: r8c::OpName, argv: Vec<AST2>) -> Result<()> {
        if ret {
            let nargs = self.pushit(argv.into_iter())?;
            self.asm_op(ChOp::new(op, vec![nargs.into()]));
            self.env_pop(nargs)?;
        } else {
            for arg in argv.into_iter() {
                self.compile(false, arg)?;
            }
        }
        Ok(())
    }

    fn compile(&mut self, ret: bool, AST2 { kind, src }: AST2) -> Result<()> {
        def_macros!($, ret, self);

        self.set_source(src.clone());

        match kind {
            M::Var(var) => match self.get_var_idx(var, &src) {
                Ok(BoundVar::Local(idx)) if ret => asm!(MOV idx),
                Ok(BoundVar::Env(idx)) if ret => asm!(GET idx),
                Ok(_) => (),
                Err(e) => match self.fns.get(&var) {
                    Some(funk) => {
                        let s = funk.args;
                        let pos = funk.pos;
                        asm!(ARGS s.nargs, s.nopt, 0, s.rest as u8);
                        asm!(CLZ pos, 0);
                    }
                    _ => return Err(e)
                }
            },
            M::If(cond, if_t, if_f) =>
                self.bt_if(ret, *cond, if_t.map(|v| *v), if_f.map(|v| *v))?,
            M::Atom(pv) => if ret { self.atom(pv)? },
            M::Progn(seq) => self.compile_seq(ret, seq)?,
            M::SymApp(op, args) => self.bt_sym_app(ret, src, op, args)?,
            M::App(op, args) => self.gapp(ret, *op, args)?,
            M::Lambda(ArgList2(spec, names), progn) =>
                self.bt_lambda(spec, names, progn, src)?,
            M::Defvar(sym, init) => {
                let spec = ArgSpec::none();
                let (pos, sz) = self.lambda(None, spec, vec![], Some(*init))?;
                let num = DEFVAR_COUNT.fetch_add(1, Ordering::SeqCst);
                let name = format!("<δ>-{num}");
                self.new_fns.push((Sym::Str(name), spec, vec![], pos, sz));
                let idx = self.new_const(PV::Nil);
                self.new_envs.push((sym, idx, pos));
                self.env.insert(sym, idx);
                if ret {
                    asm!(GET idx);
                }
            },
            M::VecSet(dst, idx, init) => self.bt_vec_set(ret, src, *dst, *idx, *init)?,
            M::Set(dst, init) => self.bt_set(ret, src, dst, *init)?,
            M::Defun(name, ArgList2(spec, names), progn) => {
                let syms = names.iter().map(|(s,_)| *s).collect();
                let (pos, sz) = self.lambda(Some(name), spec, names, progn)?;
                self.new_fns.push((Sym::Id(name), spec, syms, pos, sz));
                self.fns.insert(name, Func { pos, sz, args: spec });
                if ret {
                    asm!(ARGS spec.nargs, spec.nopt, 0, spec.rest as u8);
                    asm!(CLZ pos, 0);
                }
            },
            M::Let(decls, progn) => {
                self.bt_let(ret, decls, progn)?
            },
            M::Loop(prog) => {
                let s: Option<iter::Empty<AST2>> = None;
                self.bt_loop(ret, prog, s)?
            },
            M::Break(arg) => self.bt_break(src, arg)?,
            M::Next => self.bt_loop_next(src)?,
            M::Catch(tag, seq) => {
                let catch = self.unit().label("catch");
                let catch_jmp = self.unit().label("catch-jmp");

                self.compile(true, *tag)?;
                asm!(CTH catch_jmp);
                self.unit().mark(catch);
                self.compile_seq(true, seq)?;
                asm!(CTHPOP);
                self.unit().mark(catch_jmp);
            }
            M::Throw(tag, arg) => {
                self.compile(true, *arg)?;
                self.compile(true, *tag)?;
                asm!(UWND);
            },
            M::Not(x) => self.opcall(ret, NOT, [x])?,
            M::Gt(x, y) => self.opcall(ret, GT, [x, y])?,
            M::Gte(x, y) => self.opcall(ret, GTE, [x, y])?,
            M::Lt(x, y) => self.opcall(ret, LT, [x, y])?,
            M::Lte(x, y) => self.opcall(ret, LTE, [x, y])?,
            M::Eq(x, y) => self.opcall(ret, EQL, [x, y])?,
            M::Eqp(x, y) => self.opcall(ret, EQP, [x, y])?,
            M::Add(args) if ret => self.binop(Builtin::Add, src, chasm!(ADD),
                                              None, Some(chasm!(INT 0)), args)?,
            M::Add(args) => self.vopcall(ret, NIL, args)?,
            M::Sub(args) if ret => self.binop(Builtin::Sub, src, chasm!(SUB),
                                              Some(chasm!(INT 0)), None, args)?,
            M::Sub(args) => self.vopcall(ret, NIL, args)?,
            M::Mul(args) if ret => self.binop(Builtin::Mul, src, chasm!(MUL),
                                              None, Some(chasm!(INT 1)), args)?,
            M::Mul(args) => self.vopcall(ret, NIL, args)?,
            M::Div(args) if ret => self.binop(Builtin::Div, src, chasm!(DIV),
                                              Some(chasm!(FLT 1.0_f32.to_bits())), None, args)?,
            M::Div(args) => self.vopcall(ret, NIL, args)?,
            M::And(args) => self.bt_and(ret, args)?,
            M::Or(args) => self.bt_or(ret, args)?,

            M::NextIter(it) => self.bt_next(ret, *it)?,
            M::Car(x) => self.opcall(ret, CAR, [x])?,
            M::Cdr(x) => self.opcall(ret, CDR, [x])?,
            M::Cons(x, y) => self.opcall(ret, CNS, [x, y])?,
            M::List(xs) => self.vopcall(ret, LST, xs)?,
            M::AppendMut(xs) => self.bt_append(ret, xs, src)?,
            M::Vector(xs) => self.vopcall(ret, VEC, xs)?,
            M::Push(vec, elem) => self.bt_vpush(ret, *vec, *elem)?,
            M::Get(vec, idx) => self.opcall(ret, VGET, [vec, idx])?,
            M::Pop(vec) => opcall_mut!(VPOP *vec),
            M::CallCC(funk) => {
                self.compile(true, *funk)?;
                asm!(CCONT 0);
                if !ret { asm!(POP 1) }
            }
            M::Bt1(op, arg) => self.bt1(ret, op, arg)?,
            M::Bt2(op, a0, a1) => self.bt2(ret, op, *a0, *a1)?,
            M::TailCall(_args) => todo!(),
        }

        Ok(())
    }

    pub fn compile_top(&mut self, code: AST2) -> Result<()> {
        self.compile(false, code)
    }

    pub fn compile_top_tail(&mut self, code: AST2) -> Result<usize> {
        let num = MODULE_COUNT.fetch_add(1, Ordering::SeqCst);
        let name = format!("<σ>-{num}");
        self.compile(true, code)?;
        self.leave_fn();
        let pos = self.code.len() + self.code_offset;
        let sz = self.end_unit()?;
        self.new_fns.push((Sym::Str(name), ArgSpec::none(), vec![], pos, sz));
        Ok(pos)
    }

    pub fn take(&mut self, vm: &mut R8VM) -> Result<()> {
        vm.mem.env.append(&mut self.consts);
        let mut ufn = mem::take(&mut self.unlinked_fns);
        for (i, op) in self.code.iter_mut().enumerate() {
            *op = match *op {
                R8C::VCALL(idx, nargs) => {
                    let sym = vm.mem.get_env(idx as usize).sym().unwrap();
                    match vm.get_func(sym) {
                        Some(funk) => {
                            funk.args.check(nargs).map_err(|e| e.op(sym))?;
                            R8C::CALL(funk.pos.try_into()?, nargs)
                        }
                        None => {
                            add_unlinked(&mut ufn, sym, self.code_offset + i);
                            *op
                        }
                    }
                },
                op => op
            };
        }
        self.unlinked_fns = ufn;
        vm.pmem.append(&mut self.code);
        vm.srctbl.append(&mut self.srctbl);
        vm.labels.extend(self.labels.drain());
        for (name, spec, names, pos, sz) in self.new_fns.drain(..) {
            let name = match name {
                Sym::Id(id) => id,
                Sym::Str(s) => vm.mem.symdb.put(s).id(),
            };
            vm.defun(name, spec, names, pos, sz);
        }
        for (name, idx, init_pos) in self.new_envs.drain(..) {
            vm.defvar(name, idx, init_pos)?;
        }
        self.set_offsets(vm);
        Ok(())
    }

    pub fn set_offsets(&mut self, vm: &R8VM) {
        self.code_offset = vm.pmem.len();
        self.const_offset = vm.mem.env.len();
    }
}
