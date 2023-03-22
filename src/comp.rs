use crate::nuke::NkSum;
use crate::nkgc::{PV, SymID};
use crate::r8vm::{R8VM, ArgSpec, r8c};
use crate::chasm::{ChOp, ChASM, ChASMOpName, Lbl, self};
use crate::error::{Error, Source};
use crate::ast::{AST2, M};
use crate::ast;
use crate::r8vm::r8c::OpName::*;
use std::collections::HashMap;
use crate::compile::*;

/**
 * Compile Value into R8C code.
 */
pub struct R8Compiler<'a> {
    asm: ChASM,
    pub(crate) estack: Vec<Env>,
    loops: Vec<LoopCtx>,
    consts: Vec<PV>,
    // FIXME: This can probably be removed
    symtbl: HashMap<SymID, isize>,
    source_tbl: SourceList,
    vm: &'a R8VM,
}

#[derive(Clone, Copy)]
struct LoopCtx {
    start: Lbl,
    end: Lbl,
    ret: bool,
    height: usize,
}

impl<'a> R8Compiler<'a> {
    pub fn new(vm: &R8VM) -> R8Compiler {
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

    pub fn globals(&self) -> Option<impl Iterator<Item = (&SymID, &usize)>> {
        self.estack.first().map(|s| s.iter_statics())
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

    fn leave_fn(&mut self) {
        self.asm.op(chasm!(RET));
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
        self.asm.op(op);
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
        let end_lbl = self.asm.label("if_end");
        let if_false_lbl = self.asm.label("if_false");
        let _jmp_loc = if flipped {
            self.asm.op(chasm!(jt if_false_lbl))
        } else {
            self.asm.op(chasm!(jn if_false_lbl))
        };
        self.compile(ret, if_t)?;
        if let Some(if_false) = if_f {
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
        self.asm.add(op.0, op.1);
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
            BoundVar::Local(idx) => self.asm.op(chasm!(MOV idx)),
            BoundVar::Env(idx) => self.asm.op(chasm!(GET idx)),
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

    fn bt_sym_app(&mut self, ret: bool, src: Source, op: SymID, args: Vec<AST2>) -> Result<(), Error> {
        if let Ok(()) = self.asm_get_var(op, &src) { // Call to closure variable
            self.with_env(|env| env.anon())?;
            let args = Some(AST2::sym(op, src)).into_iter()
                                               .chain(args.into_iter());
            self.gen_call_nargs(ret, (r8c::OpName::CLZCALL, &mut [0.into()]),
                                0, args)?;
            self.env_pop(1);
        } else { // Call to symbol (virtual call)
            self.gen_call_nargs(ret, (r8c::OpName::VCALL,
                                      &mut [op.into(), 0.into()]),
                                1, args.into_iter());
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

    fn compile(&mut self, ret: bool, AST2 { kind, src }: AST2) -> Result<(), Error> {
        self.set_source(src.clone());

        match kind {
            ast::M::If(cond, if_t, if_f) =>
                self.bt_if(ret, *cond, if_t.map(|v| *v), if_f.map(|v| *v))?,
            ast::M::Atom(pv) => {
                let idx = self.consts.len();
                self.consts.push(pv);
                self.asm_op(chasm!(INST(idx)));
            },
            ast::M::Progn(seq) => self.compile_seq(ret, seq.into_iter())?,
            ast::M::SymApp(op, args) => self.bt_sym_app(ret, src, op, args)?,
            ast::M::App(op, args) => self.gapp(ret, *op, args)?,
            ast::M::Lambda(_, _) => todo!(),
            ast::M::Defvar(_, _) => todo!(),
            ast::M::Set(_, _) => todo!(),
            ast::M::Defun(_, _, _) => todo!(),
            ast::M::Let(_, _) => todo!(),
            ast::M::Loop(_) => todo!(),
            ast::M::Break => todo!(),
            ast::M::Next => todo!(),
            ast::M::Throw(_) => todo!(),
            ast::M::Not(_) => todo!(),
            ast::M::And(_) => todo!(),
            ast::M::Or(_) => todo!(),
            ast::M::Gt(_, _) => todo!(),
            ast::M::Gte(_, _) => todo!(),
            ast::M::Lt(_, _) => todo!(),
            ast::M::Lte(_, _) => todo!(),
            ast::M::Eq(_, _) => todo!(),
            ast::M::Eqp(_, _) => todo!(),
            ast::M::Add(_) => todo!(),
            ast::M::Sub(_) => todo!(),
            ast::M::Mul(_) => todo!(),
            ast::M::Div(_) => todo!(),
            ast::M::NextIter(_) => todo!(),
            ast::M::Car(_) => todo!(),
            ast::M::Cdr(_) => todo!(),
            ast::M::Cons(_, _) => todo!(),
            ast::M::List(_) => todo!(),
            ast::M::Append(_) => todo!(),
            ast::M::Vector(_) => todo!(),
            ast::M::Push(_, _) => todo!(),
            ast::M::Get(_, _) => todo!(),
            ast::M::Pop(_) => todo!(),
            ast::M::CallCC(_) => todo!(),
        }

        Ok(())
    }
}