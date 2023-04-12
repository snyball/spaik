#![allow(dead_code)]

use std::mem::take;

use fnv::FnvHashSet;

use crate::{ast::{AST2, M, Visitor, VarDecl, Visitable}, nkgc::PV, error::Source, SymID};

#[derive(Debug, Default)]
pub struct Optomat {
    changed: bool,
    force: bool,
    varmod: FnvHashSet<SymID>,
}

impl Optomat {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
struct LowerConst(SymID, PV);

impl Visitor for LowerConst {
    fn visit(&mut self, elem: &mut AST2) -> crate::IResult<()> {
        match elem.kind {
            M::Set(ref mut name, _) if *name == self.0 => {
                bail!(None)
            }
            M::Var(name) if name == self.0 => *elem = AST2 {
                kind: self.1.into(),
                src: elem.src.clone()
            },
            _ => elem.visit(self)?
        }
        Ok(())
    }
}

impl Visitor for Optomat {
    fn visit(&mut self, elem: &mut AST2) -> crate::IResult<()> {
        match elem.kind {
            // Lowering
            M::Let(ref mut vars, ref mut body) => {
                let consts = vars.iter().filter_map(|VarDecl(sym, _s, init)| {
                    init.imm().map(|(atom, _s)| LowerConst(*sym, atom))
                });
                let mut dead_vars = consts.clone()
                                          .filter(|p| !self.varmod.contains(&p.0))
                                          .map(|LowerConst(sym, _)| sym)
                                          .collect::<FnvHashSet<_>>();
                for mut lower in consts {
                    for pt in body.iter_mut() {
                        match lower.visit(pt) {
                            Ok(_) => (),
                            Err(e) if e.is_none() => {
                                self.varmod.insert(lower.0);
                                dead_vars.remove(&lower.0);
                                break;
                            },
                            e => return e
                        }
                    }
                }
                vars.retain(|VarDecl(name, _, _)| !dead_vars.contains(name));
                if vars.is_empty() {
                    elem.kind = M::Progn(take(body));
                }
                elem.visit(self)?;
            }
            M::Add(ref mut xs) => {
                let mut consts = xs.iter_mut().filter_map(|x| x.atom());
                let Some((mut s, src)) = consts.next() else {
                    return xs.visit(self)
                };
                let src = src.clone();
                for (x, src) in consts {
                    s.add_mut(&x).map_err(|e| e.src(src.clone()))?;
                }
                xs.retain(|x| !x.is_atom());
                let s_elem = AST2 { src, kind: M::Atom(s) };
                if xs.is_empty() {
                    *elem = s_elem;
                } else {
                    xs.push(s_elem);
                }
            }
            _ => elem.visit(self)?,
        }
        Ok(())
    }
}

impl AST2 {
    fn atom(&self) -> Option<(PV, &Source)> {
        match self.kind {
            M::Atom(atom) => Some((atom, &self.src)),
            _ => None,
        }
    }

    fn imm(&self) -> Option<(PV, &Source)> {
        match self.kind {
            M::Atom(atom) => match atom {
                PV::Ref(_) => None,
                pv => Some((pv, &self.src))
            }
            _ => None,
        }
    }

    fn bool(&self) -> Option<bool> {
        match self.kind {
            M::Atom(atom) => Some(atom.into()),
            _ => None,
        }
    }
}
