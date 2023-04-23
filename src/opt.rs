use std::mem::{take, replace};

use fnv::FnvHashSet;

use crate::{ast::{AST2, M, Visitor, VarDecl, Visitable}, nkgc::PV, error::Source, SymID, Builtin};

#[derive(Debug, Default)]
pub struct Optomat {
    varmod: FnvHashSet<SymID>,
}

impl Optomat {
    pub fn new() -> Self {
        Self::default()
    }
}

struct IsModified(SymID);

impl Visitor for IsModified {
    fn visit(&mut self, elem: &mut AST2) -> crate::Result<()> {
        match elem.kind {
            M::Set(ref mut name, _) if *name == self.0 => bail!(None),
            _ => elem.visit(self)
        }
    }
}

#[derive(Debug)]
struct LowerConst(SymID, PV);

impl Visitor for LowerConst {
    fn visit(&mut self, elem: &mut AST2) -> crate::Result<()> {
        match elem.kind {
            M::Loop(ref mut body) => {
                let mut modf = IsModified(self.0);
                body.visit(&mut modf)?;
                body.visit(self)?;
            }
            M::Bt2(Builtin::LoopWithEpilogue, ref mut bod, ref mut epl) => {
                let mut modf = IsModified(self.0);
                modf.visit(bod)?;
                modf.visit(epl)?;
                self.visit(bod)?;
                self.visit(epl)?;
            }
            M::Set(ref mut name, _) if *name == self.0 => bail!(None),
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
    fn visit(&mut self, elem: &mut AST2) -> crate::Result<()> {
        macro_rules! cmp_op {
            ($a:ident $m:ident $b:ident $($q:tt)*) => {
                match ($a.atom(), $b.atom()) {
                    (Some((a, _)), Some((b, _))) =>
                        *elem = AST2 { src: elem.src.clone(),
                                       kind: M::Atom(a.$m(&b) $($q)*) },
                    _ => { self.visit($a)?;
                           self.visit($b)?; }
                }
            };
        }
        macro_rules! sum_op {
            ($xs:ident $m:ident) => {{
                $xs.visit(self)?;
                let mut consts = $xs.iter_mut().filter_map(|x| x.atom());
                let Some((mut s, src)) = consts.next() else {
                    return Ok(())
                };
                let src = src.clone();
                for (x, src) in consts {
                    s.$m(&x).map_err(|e| e.src(src.clone()))?;
                }
                $xs.retain(|x| !x.is_atom());
                let s_elem = AST2 { src, kind: M::Atom(s) };
                if $xs.is_empty() {
                    *elem = s_elem;
                } else {
                    $xs.push(s_elem);
                }
            }};
        }
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
                            Ok(_) => {}
                            Err(e) if e.is_none() => {
                                self.varmod.insert(lower.0);
                                dead_vars.remove(&lower.0);
                                break;
                            }
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
            M::Add(ref mut xs) => sum_op!(xs add_mut),
            M::Mul(ref mut xs) => sum_op!(xs mul_mut),
            M::If(ref mut cond, ref mut ift, ref mut ifn) => {
                self.visit(cond)?;
                if let Some((cond, src)) = cond.atom() {
                    let nil = || Box::new(AST2 { src: src.clone(),
                                                 kind: M::Atom(PV::Nil) });
                    if cond.into() {
                        if let Some(ref mut ift) = ift { ift.visit(self)? }
                        *elem = *ift.take().unwrap_or_else(nil);
                    } else {
                        if let Some(ref mut ifn) = ifn { ifn.visit(self)? }
                        *elem = *ifn.take().unwrap_or_else(nil);
                    }
                } else {
                    self.visit(cond)?;
                    if let Some(ref mut ift) = ift { self.visit(ift)? }
                    if let Some(ref mut ifn) = ifn { self.visit(ifn)? }
                }
            }
            M::Gt(ref mut a, ref mut b) => cmp_op!(a gt b ?),
            M::Gte(ref mut a, ref mut b) => cmp_op!(a gte b ?),
            M::Lt(ref mut a, ref mut b) => cmp_op!(a lt b ?),
            M::Lte(ref mut a, ref mut b) => cmp_op!(a lte b ?),
            M::Eq(ref mut a, ref mut b) => cmp_op!(a eq b .into()),
            M::Eqp(ref mut a, ref mut b) => cmp_op!(a equalp b .into()),
            _ => elem.visit(self)?,
        }
        Ok(())
    }
}

struct FindLoopBreak<F: FnMut(&mut AST2) -> crate::Result<()>>(F);

impl<F> Visitor for FindLoopBreak<F>
    where F: FnMut(&mut AST2) -> crate::Result<()>
{
    fn visit(&mut self, elem: &mut AST2) -> crate::Result<()> {
        match elem.kind {
            M::Break(Some(ref mut x)) => (self.0)(x)?,
            M::Loop(_) => (),
            _ => (),
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct TCOptomat {
    names: Vec<SymID>,
}

impl Visitor for TCOptomat {
    fn visit(&mut self, elem: &mut AST2) -> crate::Result<()> {
        match elem.kind {
            M::Defun(name, _, ref mut body) => {
                self.names.push(name);
                if let Some(e) = body.last_mut() {
                    self.visit(e)?;
                }
                self.names.pop().unwrap();
            }
            M::Lambda(_, _) => (),
            M::If(_, ref mut ift, ref mut ifn) => {
                if let Some(e) = ift {
                    self.visit(e)?;
                }
                if let Some(e) = ifn {
                    self.visit(e)?;
                }
            }
            M::Loop(ref mut body_ref) => {
                let mut body = take(body_ref);
                let mut visitor = FindLoopBreak(|x| self.visit(x));
                body.visit(&mut visitor)?;
                drop(replace(body_ref, body));
            }
            M::SymApp(ref mut name, ref mut body)
                if Some(*name) == self.names.last().cloned() => {
                *elem = AST2 { src: elem.src.clone(),
                               kind: M::TailCall(take(body)) }
            }
            _ if self.names.is_empty() => elem.visit(self)?,
            _ => ()
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
}
