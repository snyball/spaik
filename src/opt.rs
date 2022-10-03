use crate::{ast::{AST2, M}, nkgc::PV, error::Source, Builtin};
use crate::error::Error;

struct ConstEval {
}

enum ConstValue<T> {
    Decided(T),
    Undecided
}

impl AST2 {
    fn eval(&mut self, force: bool) -> Result<bool, Error> {
        match &mut self.kind {
            M::If(cond, ifa, ifb) => {
                cond.eval(force)?;
                if let Some(b) = cond.bool() {
                    if b {
                        let mut ifa = ifa.take().expect("illegal if-expr");
                        ifa.eval(force)?;
                        *self = *ifa;
                    } else {
                        *self = if let Some(mut ifb) = ifb.take() {
                            ifb.eval(force)?;
                            *ifb
                        } else {
                            M::Atom(PV::Nil).ast(self.src.clone())
                        }
                    }
                } else {
                    if let Some(ifa) = ifa { ifa.eval(force)?; }
                    if let Some(ifb) = ifb { ifb.eval(force)?; }
                }
            }
            M::Progn(pr) => if pr.len() == 1 {
                *self = pr.pop().unwrap();
                self.eval(force)?;
                return Ok(true);
            } else {
                let mut change = false;
                for arg in pr.iter_mut() {
                    change = arg.eval(force)?;
                }
                // Only the last value of progn will change the value of the expression
                return Ok(change);
            }
            M::Add(xs) => {
                if xs.len() == 1 {
                    *self = xs.pop().unwrap();
                    return Ok(true);
                }
                let mut had_change = force;
                for x in xs.iter_mut() {
                    had_change = had_change || x.eval(force)?;
                }
                if !had_change {
                    return Ok(false);
                }
                let mut sum = PV::Int(0);
                let mut have_sum = false;
                let mut err = None;
                xs.retain(|x| x.atom().map(|(n, src)| {
                    match sum.add(&n).map_err(|e| e.src(src.clone())) {
                        Ok(x) => sum = x,
                        Err(e) => err = Some(e),
                    }
                    have_sum = true;
                }).is_none());
                if let Some(e) = err {
                    return Err(e.op(Builtin::Add.sym()));
                }
                if have_sum {
                    xs.push(M::Atom(sum).ast(self.src.clone()));
                    return Ok(true);
                }
            }
            _ => ()
        }
        Ok(false)
    }

    fn atom(&self) -> Option<(PV, &Source)> {
        match self.kind {
            M::Atom(atom) => Some((atom, &self.src)),
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
