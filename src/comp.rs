use chasm::LblMap;

use crate::nuke::NkSum;
use crate::nkgc::{PV, SymID};
use crate::r8vm::{R8VM, ArgSpec, r8c};
use crate::chasm::{ChOp, ChASM, ChASMOpName, Lbl, self};
use crate::error::{Error, Source};
use crate::ast::{AST2, M, Prog, Progn, M2};
use crate::{ast, SPV};
use crate::r8vm::r8c::{OpName::*, Op as R8C};
use std::collections::HashMap;
use crate::compile::*;

/**
 * Compile Value into R8C code.
 */
pub struct R8Compiler {
    labels: LblMap,
    code: Vec<R8C>,
    units: Vec<ChASM>,
    source_tbl: SourceList,
    pub(crate) estack: Vec<Env>,
    loops: Vec<LoopCtx>,
    const_offset: usize,
    consts: Vec<PV>,
}

#[derive(Clone, Copy)]
struct LoopCtx {
    start: Lbl,
    end: Lbl,
    ret: bool,
    height: usize,
}

pub type Linked = (Vec<R8C>,
                   LblLookup,
                   Vec<PV>,
                   SourceList);

impl R8Compiler {
    pub fn new(vm: &R8VM) -> R8Compiler {
        let units = vec![ChASM::new()];
        R8Compiler {
            const_offset: 0,
            estack: Default::default(),
            labels: Default::default(),
            consts: Default::default(),
            loops: Default::default(),
            source_tbl: Default::default(),
            code: Default::default(),
            units,
        }
    }

    pub fn unit(&mut self) -> &mut ChASM {
        self.units.last_mut().expect("No unit to save asm to")
    }

    pub fn end_unit(&mut self) -> Result<usize, Error> {
        let len = self.code.len();
        self.units.pop()
                  .expect("No unit to end")
                  .link_into(&mut self.code, len, &mut self.labels)?;
        Ok(len)
    }

    pub fn begin_unit(&mut self) {
        self.units.push(ChASM::new())
    }

    pub fn set_source(&mut self, src: Source) {
        match self.source_tbl.last() {
            Some((_, last_src)) if *last_src == src => (),
            _ => {
                let idx = self.unit().len();
                self.source_tbl.push((idx, src));
            }
        }
    }

    pub fn globals(&self) -> Option<impl Iterator<Item = (&SymID, &usize)>> {
        self.estack.first().map(|s| s.iter_statics())
    }

    pub fn link(mut self) -> Result<Linked, Error> {
        let len = self.unit().len() as isize;
        let tbl = Default::default();
        let (asm, labels) = self.units.pop().unwrap().link::<R8C>(&tbl, len)?;
        Ok((asm, labels, self.consts, self.source_tbl))
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
            self.unit().op(chasm!(SAV 2));
            if spec.has_opt() {
                self.unit().op(chasm!(TOP spec.nargs));
                self.unit().op(chasm!(JV 1, spec.nopt));
                for _ in 0..spec.nopt {
                    self.unit().op(chasm!(NIL));
                }
            }
            if spec.has_body() {
                self.unit().op(chasm!(TOP spec.nargs + spec.nopt));
                self.unit().op(chasm!(VLIST));
            }
            if spec.has_env() {
                self.unit().op(chasm!(CLZEXP));
            }
            self.unit().op(chasm!(RST));
        }
        Ok(())
    }

    fn leave_fn(&mut self) {
        self.unit().op(chasm!(RET));
        self.estack.pop();
    }

    fn with_env<T>(&mut self, f: impl Fn(&mut Env) -> T) -> Result<T, Error> {
        self.estack
            .last_mut()
            .map(f)
            .ok_or_else(|| "No environment".into())
    }

    #[inline]
    fn asm_op(&mut self, op: ChOp) {
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
    fn push(&mut self, code: AST2) -> Result<usize, Error> {
        self.compile(true, code)?;
        self.with_env(|env| env.anon())
    }

    fn pushit<'z>(&mut self, args: impl Iterator<Item = AST2>) -> Result<usize, Error> {
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
    pub fn argument_clinic(mut code: AST2) -> (bool, AST2) {
        let mut flipped = false;
        while let AST2 { kind: M::Not(sub), .. } = code {
            flipped = !flipped;
            code = *sub;
        }
        (flipped, code)
    }

    fn bt_if(&mut self, ret: bool,
             cond: AST2, if_t: Option<AST2>, if_f: Option<AST2>
    ) -> Result<(), Error> {
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
        Ok(())
    }

    fn compile_seq<'z>(&mut self,
                       ret: bool,
                       mut seq: impl Iterator<Item = AST2>
    ) -> Result<(), Error> {
        let Some(mut last) = seq.next() else {
            if ret { self.asm_op(chasm!(NIL)) }
            return Ok(())
        };
        while let Some(nx) = seq.next() {
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
                      args: impl Iterator<Item = AST2>) -> Result<(), Error> {
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
                   src: &Source) -> Result<(), Error> {
        match self.get_var_idx(var, src)? {
            BoundVar::Local(idx) => self.unit().op(chasm!(MOV idx)),
            BoundVar::Env(idx) => self.unit().op(chasm!(GET idx)),
        };
        Ok(())
    }

    fn get_var_idx(&mut self,
                   var: SymID,
                   src: &Source) -> Result<BoundVar, Error> {
        if let Some(idx) = self.with_env(|env| env.get_idx(var))? {
            return Ok(BoundVar::Local(idx as u32));
        }
        for env in self.estack.iter().rev() {
            if let Some(idx) = env.get_env_idx(var) {
                return Ok(BoundVar::Env(idx as u32))
            }
        }
        // if let Some(idx) = self.vm.get_env_global(var) {
        //     return Ok(BoundVar::Env(idx as u32))
        // }
        err_src!(src.clone(), UndefinedVariable, var)
    }

    fn asm_set_var_idx(&mut self, idx: &BoundVar) -> Result<(), Error> {
        match idx {
            BoundVar::Local(idx) => self.unit().op(chasm!(STR *idx)),
            BoundVar::Env(idx) => self.unit().op(chasm!(SET *idx)),
        };
        Ok(())
    }

    fn bt_sym_app(&mut self, ret: bool, src: Source, op: SymID, args: Vec<AST2>) -> Result<(), Error> {
        if let Ok(()) = self.asm_get_var(op, &src) { // Call to closure variable
            self.with_env(|env| env.anon())?;
            let args = Some(AST2::sym(op, src)).into_iter()
                                               .chain(args.into_iter());
            self.gen_call_nargs(ret, (r8c::OpName::CLZCALL, &mut [0.into()]),
                                0, args)?;
            self.env_pop(1).unwrap();
        } else { // Call to symbol (virtual call)
            self.gen_call_nargs(ret, (r8c::OpName::VCALL,
                                      &mut [op.into(), 0.into()]),
                                1, args.into_iter())?;
        }
        Ok(())
    }

    fn gapp(&mut self, ret: bool, op: AST2, args: Vec<AST2>) -> Result<(), Error> {
        if !matches!(op.type_of(), Builtin::Unknown | Builtin::Lambda) {
            return Err(error!(TypeError,
                              expect: Builtin::Lambda.sym(),
                              got: op.type_of().sym())
                       .src(op.src.clone()).argn(0).op(Builtin::Apply.sym()))
        }
        self.compile(true, op)?;
        self.with_env(|env| env.anon())?; // closure
        self.gen_call_nargs(ret, (r8c::OpName::CLZCALL, &mut [0.into()]),
                            0, args.into_iter())?;
        self.env_pop(1)
    }

    pub fn take_consts(&mut self, into: &mut Vec<PV>) {
        self.const_offset += self.consts.len();
        into.extend(self.consts.drain(..))
    }

    pub fn bt_set(&mut self,
                  ret: bool,
                  src: Source,
                  dst: SymID,
                  init: Prog) -> Result<(), Error> {
        let bound = self.get_var_idx(dst, &src)?;
        if let BoundVar::Local(idx) = bound {
            let mut inplace_op = |op, val: i64| {
                self.unit().add(op, &[idx.into(), val.into()]);
                if ret { self.asm_op(chasm!(MOV idx)) }
            };
            match init.kind.binary() {
                // Handle (set x (+ x 2)) => INC x, 2
                //        (set x (+ 1 x)) => INC x, 1
                //        (set x (- x 1)) => DEC x, 1
                //        (set x (- 1 x)) => Not special
                Some(M2::Add(M::Atom(PV::Sym(sym)), M::Atom(PV::Int(num)))) |
                Some(M2::Add(M::Atom(PV::Int(num)), M::Atom(PV::Sym(sym))))
                    if sym == dst => {
                    inplace_op(INC, num);
                    return Ok(())
                }
                Some(M2::Sub(M::Atom(PV::Sym(sym)), M::Atom(PV::Int(num))))
                    if sym == dst => {
                    inplace_op(DEC, num);
                    return Ok(())
                }
                _ => ()
            }
        }
        self.compile(true, *init)?;
        if ret { self.asm_op(chasm!(DUP)) }
        // NOTE!: Currently the variable index has no reason to change
        //        between the call to get_var_idx and asm_set_var_idx.
        //        Should that change this will become invalid:
        self.asm_set_var_idx(&bound)
    }

    fn compile(&mut self, ret: bool, AST2 { kind, src }: AST2) -> Result<(), Error> {
        self.set_source(src.clone());

        match kind {
            M::If(cond, if_t, if_f) =>
                self.bt_if(ret, *cond, if_t.map(|v| *v), if_f.map(|v| *v))?,
            M::Atom(pv) => {
                let idx = self.const_offset + self.consts.len();
                self.consts.push(pv);
                self.unit().op(chasm!(INST(idx)));
            },
            M::Progn(seq) => self.compile_seq(ret, seq.into_iter())?,
            M::SymApp(op, args) => self.bt_sym_app(ret, src, op, args)?,
            M::App(op, args) => self.gapp(ret, *op, args)?,
            M::Lambda(_, _) => todo!(),
            M::Defvar(_, _) => todo!(),
            M::Set(dst, init) => self.bt_set(ret, src, dst, init)?,
            M::Defun(_, _, _) => todo!(),
            M::Let(_, _) => todo!(),
            M::Loop(_) => todo!(),
            M::Break => todo!(),
            M::Next => todo!(),
            M::Throw(_) => todo!(),
            M::Not(_) => todo!(),
            M::And(_) => todo!(),
            M::Or(_) => todo!(),
            M::Gt(_, _) => todo!(),
            M::Gte(_, _) => todo!(),
            M::Lt(_, _) => todo!(),
            M::Lte(_, _) => todo!(),
            M::Eq(_, _) => todo!(),
            M::Eqp(_, _) => todo!(),
            M::Add(_) => todo!(),
            M::Sub(_) => todo!(),
            M::Mul(_) => todo!(),
            M::Div(_) => todo!(),
            M::NextIter(_) => todo!(),
            M::Car(_) => todo!(),
            M::Cdr(_) => todo!(),
            M::Cons(_, _) => todo!(),
            M::List(_) => todo!(),
            M::Append(_) => todo!(),
            M::Vector(_) => todo!(),
            M::Push(_, _) => todo!(),
            M::Get(_, _) => todo!(),
            M::Pop(_) => todo!(),
            M::CallCC(_) => todo!(),
        }

        Ok(())
    }

    pub fn compile_top(self, ret: bool, code: AST2) -> Result<Linked, Error> {
        // self.compile(ret, code);
        // self.link()
        todo!()
    }
}
