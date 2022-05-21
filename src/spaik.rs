use crate::{r8vm::R8VM, subrs::{Subr, IntoLisp, RefIntoLisp, Ignore}, nkgc::{SymID, SPV, PV}, error::Error, fmt::LispFmt, sym_db::SymDB, compile::Builtin};

/// A Spaik Context
pub struct Spaik {
    vm: R8VM
}

pub struct VarName {
    sym: SymID,
}

pub trait VMInto<T> {
    fn vm_into(self, vm: &mut R8VM) -> T;
}

impl VMInto<SymID> for &str {
    fn vm_into(self, vm: &mut R8VM) -> SymID {
        vm.mem.put_sym(self)
    }
}

struct ArgList<'a, 'b: 'a>(&'a [&'b dyn RefIntoLisp]);

impl Spaik {
    pub fn new() -> Result<Spaik, Error> {
        let mut vm = Spaik {
            vm: R8VM::new()
        };
        vm.load("stdlib")?;
        Ok(vm)
    }

    pub fn register(&mut self, func: Box<dyn Subr>) {
        self.set(func.name(), func);
    }

    pub fn set<V, T>(&mut self, var: V, obj: T)
        where V: VMInto<SymID>, T: IntoLisp
    {
        let var = var.vm_into(&mut self.vm);
        self.vm.set(var, obj).unwrap();
    }

    pub fn eval<E, R>(&mut self, expr: E) -> Result<R, Error>
        where E: AsRef<str>,
              R: TryFrom<PV, Error = Error>
    {
        self.vm.eval(expr.as_ref())
               .and_then(|pv| pv.try_into())
    }

    pub fn exec<E>(&mut self, expr: E) -> Result<(), Error>
        where E: AsRef<str>
    {
        let _: Ignore = self.eval(expr)?;
        Ok(())
    }

    pub fn load<V>(&mut self, lib: V) -> Result<SymID, Error>
        where V: VMInto<SymID>
    {
        let lib = lib.vm_into(&mut self.vm);
        self.vm.load(lib)
    }

    pub fn call<V, R>(&mut self,
                      sym: V,
                      args: &[&dyn RefIntoLisp])
                      -> Result<R, Error>
        where V: VMInto<SymID>,
              R: TryFrom<PV, Error = Error>
    {
        let sym = sym.vm_into(&mut self.vm);
        let args_pv = args.iter()
                          .map(|v| v.ref_into_pv(&mut self.vm.mem))
                          .collect::<Result<Vec<PV>, _>>()?;
        self.vm.raw_call(sym, &args_pv[..]).and_then(|pv| {
            let r = pv.try_into()?;
            Ok(r)
        })
    }
}

#[macro_export]
macro_rules! args {
    ($($arg:expr),*) => {
        &[$(&$arg as &dyn RefIntoLisp),*]
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn api_eval_add_numbers() {
        let mut vm = Spaik::new().unwrap();
        let result: i32 = vm.eval("(+ 2 3)").unwrap();
        assert_eq!(result, 5);
        let result: i16 = vm.eval("(+ 2 3)").unwrap();
        assert_eq!(result, 5);
        let result: f32 = vm.eval("(+ 2.0 3)").unwrap();
        assert_eq!(result, 5.0);
    }

    #[test]
    fn api_func_call() {
        let mut vm = Spaik::new().unwrap();
        vm.exec(
            "(defun plus (&rest xs) (let ((s 0)) (dolist (x xs) (set s (+ s x))) s))"
        ).unwrap();
        let x = 1;
        let y = 2;
        let z = 3;
        let w = 4;
        let result: i32 = vm.call("plus", args![x, y, z, w, 5]).unwrap();
        assert_eq!(result, 15);
    }
}
