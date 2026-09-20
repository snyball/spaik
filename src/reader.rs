use std::mem;

use crate::ast::Excavator;
use crate::comp::R8Compiler;
use crate::error::{LineCol, Meta, Source, SourceFileName, SyntaxErrorKind};
use crate::nkgc::Arena;
use crate::r8vm::R8VM;
use crate::string_parse::string_parse;
use crate::tok::Token;
use crate::tokit::Toker;
use crate::{tokit, Builtin, Result};
use crate::{SymID, PV};
use crate::utils::HMap;

pub struct Sexpert<'a, 'b, S: Sexper> {
    sexper: S,
    toker: tokit::Toker<'a, 'b>,
    reader_macros: HMap<String, SymID>,
    file: SourceFileName,
}

pub trait Sexper {
    fn tlsexpre(&mut self, vm: &mut R8VM, num: u32, dot: bool) -> Result<PV>;
    fn sexpre(&mut self, vm: &mut R8VM, v: PV) -> Result<PV>;
    fn sexp(&mut self, vm: &mut R8VM, v: PV, is_tail: bool, src: Source) -> Result<()>;
    fn tlatom(&mut self, vm: &mut R8VM, v: PV, is_tail: bool, src: Source) -> Result<()>;
    fn finalize(self, vm: &mut R8VM) -> Result<PV>;
}

fn sexpr_modifier_bt(tok: &str) -> Option<Builtin> {
    Some(match tok {
        "'" => Builtin::Quote,
        "`" => Builtin::Quasi,
        "," => Builtin::Unquote,
        ",@" => Builtin::USplice,
        _ => return None,
    })
}

impl<'a, 'b, S: Sexper> Sexpert<'a, 'b, S> {
    pub fn new(sexper: S, toker: Toker<'a, 'b>, reader_macros: HMap<String, SymID>, file: SourceFileName) -> Self {
        Self {
            sexper, toker, reader_macros, file
        }
    }

    pub fn read(mut self, vm: &mut R8VM) -> Result<PV> {
        let mut mods: Vec<SymID> = vec![];
        let mut close = vec![];
        let mut pmods = vec![];
        let mut dots = vec![];
        let mut dot = None;
        let mut num: u32 = 0;
        let mut srcs = vec![];
        let mut src_idxs = vec![0];
        macro_rules! wrap {
            ($push:expr) => {{
                $push;
                while let Some(op) = mods.pop() {
                    let p = vm.mem.pop().expect("No expr to wrap");
                    vm.mem.push(PV::Sym(op));
                    vm.mem.push(p);
                    vm.mem.list(2);
                }
            }};
        }
        macro_rules! assert_no_trailing {
            ($($meta:expr),*) => {
                if !mods.is_empty() {
                    let mods = mods.into_iter()
                                   .map(|s| s.to_string())
                                   .collect::<Vec<_>>()
                                   .join("");
                    return Err(error!(TrailingModifiers, mods)$(.amend($meta))*);
                }
            };
        }
        while let Some(tok) = self.toker.next() {
            let Token { line, col, text } = tok;
            srcs.push(LineCol { line, col });
            match text {
                "(" => {
                    src_idxs.push(srcs.len());
                    pmods.push(mem::take(&mut mods));
                    close.push(num + 1);
                    dots.push(dot);
                    dot = None;
                    num = 0;
                }
                ")" if close.is_empty() => bail!(TrailingDelimiter { close: ")" }),
                "." if close.is_empty() => bail!(OutsideContext {
                    ctx: Builtin::List,
                    op: Builtin::ConsDot
                }),
                "." if num == 0 => bail!(SyntaxError(SyntaxErrorKind::DotAtStartOfList)),
                "." if dot.is_some() => bail!(SyntaxError(SyntaxErrorKind::DotAfterDot)),
                "." => {
                    if self.toker.peek().map(|t| t.text == ")").unwrap_or_default() {
                        bail!(SyntaxError(SyntaxErrorKind::DotAtEndOfList))
                    }

                    if !mods.is_empty() {
                        bail!(SyntaxError(SyntaxErrorKind::ModifierBeforeDot))
                    }

                    dot = Some(num)
                },
                ")" => {
                    if let Some(dot_at) = dot {
                        if dot_at != num-1 {
                            bail!(SyntaxError(SyntaxErrorKind::MoreThanOneElemAfterDot))
                        }
                    }
                    assert_no_trailing!(Meta::Source(LineCol { line, col }));
                    let src_idx = src_idxs.pop().unwrap();
                    let fst_src = srcs[src_idx].into_source(self.file.clone());
                    let cur_srcs = srcs.drain(src_idx..)
                                       .map(|lc| lc.into_source(self.file.clone()));
                    mods = pmods.pop().expect("Unable to wrap expr");
                    if num > 0 && close.len() == 1 {
                        let v = if mods.is_empty() {
                            let idx = vm.mem.stack.len() - num as usize;
                            let stack = mem::take(&mut vm.mem.stack);
                            for (pv, src) in stack[idx..].iter().zip(cur_srcs) {
                                pv.tag(&mut vm.mem, src);
                            }
                            let _ = mem::replace(&mut vm.mem.stack, stack);
                            self.sexper.tlsexpre(vm, num, dot.is_some())?
                        } else {
                            wrap!(vm.mem.list_dot_srcs(num, cur_srcs, dot.is_some()));
                            let pv = vm.mem.pop().unwrap();
                            self.sexper.sexpre(vm, pv)?
                        };
                        self.sexper.sexp(vm, v, self.toker.peek().is_none(), fst_src)?;
                    } else {
                        wrap!(vm.mem.list_dot_srcs(num, cur_srcs, dot.is_some()));
                    }

                    dot = dots.pop().unwrap();
                    num = close.pop()
                               .ok_or_else(
                                   || error!(TrailingDelimiter, close: ")")
                                       .amend(Meta::Source(LineCol { line, col })))?;
                }
                _ => {
                    let sexpr_mod = sexpr_modifier_bt(text)
                        .map(|b| b.sym_id())
                        .or_else(|| {
                            self.reader_macros.get(text).copied()
                        });
                    let pv = if let Some(m) = sexpr_mod {
                        mods.push(m);
                        continue;
                    } else if let Ok(int) = text.parse() {
                        PV::Int(int)
                    } else if let Ok(num) = text.parse() {
                        let mut tit = text.chars().peekable();
                        let fst = tit.peek();
                        if fst == Some(&'-') || fst == Some(&'+') {
                            tit.next();
                        }
                        if tit.all(|x| x.is_digit(10)) {
                            bail!(IntegerLiteralTooLarge {
                                lit: text.to_string()
                            })
                        }
                        PV::Real(num)
                    } else if let Some(strg) = tok.inner_str() {
                        vm.mem.put_pv(string_parse(&strg)?)
                    } else if text == "true" {
                        PV::Bool(true)
                    } else if text == "false" {
                        PV::Bool(false)
                    } else if text == "nil" {
                        PV::Nil
                    } else {
                        PV::Sym(vm.mem.symdb.put_ref(text).id())
                    };

                    if !close.is_empty() {
                        wrap!(vm.mem.push(pv));
                    } else {
                        wrap!(vm.mem.push(pv));
                        let pv = vm.mem.pop().unwrap();
                        let src = LineCol { line, col }.into_source(self.file.clone());
                        self.sexper.tlatom(vm, pv, self.toker.peek().is_none(), src)?;
                    }

                    num += 1;
                }
            }
        }
        self.toker.check_error().map_err(|e| if let Some(file) = self.file.clone() {
            e.amend(Meta::SourceFile(file))
        } else { e })?;
        if !close.is_empty() {
            bail!(UnclosedDelimiter { open: "(" })
        }
        assert_no_trailing!();
        self.sexper.finalize(vm)
    }
}
