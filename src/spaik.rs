//! SPAIK public API

use crate::nuke::Fissile;
use crate::r8vm::{R8VM, Args};
use crate::sym_db::SymDB;
use crate::error::Error;
use crate::nkgc::{SymID, PV, ObjRef};
use crate::subrs::{Subr, IntoLisp, Ignore};

/// A Spaik Context
pub struct Spaik {
    vm: R8VM
}

pub trait VMInto<T> {
    fn vm_into(self, vm: &mut R8VM) -> T;
}

impl VMInto<SymID> for &str {
    fn vm_into(self, vm: &mut R8VM) -> SymID {
        vm.mem.put_sym(self)
    }
}

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

    pub fn get_clone<V, T>(&mut self, var: V) -> Result<T, Error>
        where V: VMInto<SymID>, T: Fissile + 'static + Clone
    {
        self.get_ref_mut(var).map(|rf: &mut T| (*rf).clone())
    }

    pub fn get_ref<'a, V, T>(&'a mut self, var: V) -> Result<&'a T, Error>
        where V: VMInto<SymID>, T: Fissile + 'static
    {
        self.get_ref_mut(var).map(|rf| &*rf)
    }

    pub fn get_ref_mut<'a, V, T>(&'a mut self, var: V) -> Result<&'a mut T, Error>
        where V: VMInto<SymID>, T: Fissile + 'static
    {
        let name = var.vm_into(&mut self.vm);
        let idx = self.vm.get_env_global(name)
                         .ok_or_else(|| error!(UndefinedVariable,
                                               var: name))?;
        let ObjRef(x): ObjRef<&mut T> = self.vm.mem.get_env(idx).try_into()?;
        Ok(x)
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

    pub fn call<V, A, R>(&mut self, sym: V, args: A) -> Result<R, Error>
        where V: VMInto<SymID>,
              A: Args,
              R: TryFrom<PV, Error = Error>,
    {
        let sym = sym.vm_into(&mut self.vm);
        self.vm.call(sym, args).and_then(|pv| {
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
    use std::fmt;

    use spaik_proc_macros::{spaikfn, Fissile};

    use crate::{nuke::{PtrMap, NkAtom, Object}, fmt::VisitSet};

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
        let result: i32 = vm.call("plus", (x, y, z, w, 5)).unwrap();
        assert_eq!(result, 15);
    }

    #[test]
    fn register_fn() {
        #[spaikfn]
        fn funky_function(x: i32, y: i32) -> i32 {
            x + 2 + y
        }

        let mut vm = Spaik::new().unwrap();
        vm.register(funky_function_obj::new());
        let result: i32 = vm.eval("(funky-function 2 8)").unwrap();
        assert_eq!(result, 12);

        // FIXME: The vm_call_with! macro should eventually support this:
        // let result: i32 = vm.call("funky-function", (4, 8)).unwrap();
        // assert_eq!(result, 14);
    }

    #[test]
    fn register_fn_mutate_struct() {
        #[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Fissile)]
        pub struct TestObj {
            x: f32,
            y: f32,
        }

        #[spaikfn]
        fn my_function(x: i32, y: i32, obj: &TestObj, obj2: &mut TestObj) -> i32 {
            let res = x + y.pow(2);
            obj2.x += obj.x;
            obj2.y += obj.y;
            res
        }

        #[spaikfn]
        fn obj_x(obj: &TestObj) -> f32 {
            obj.x
        }

        #[spaikfn]
        fn obj_y(obj: &TestObj) -> f32 {
            obj.y
        }

        let mut vm = Spaik::new().unwrap();
        vm.register(my_function_obj::new());
        vm.register(obj_x_obj::new());
        vm.register(obj_y_obj::new());
        let src_obj = TestObj { x: 1.0, y: 3.0 };
        let dst_obj = TestObj { x: 1.0, y: 2.0 };
        vm.set("src-obj", src_obj.clone());
        vm.set("dst-obj", dst_obj.clone());
        vm.exec("(my-function 1 1 src-obj dst-obj)").unwrap();
        vm.exec("(println dst-obj)").unwrap();
        let x: f32 = vm.eval("(obj-x dst-obj)").unwrap();
        let y: f32 = vm.eval("(obj-y dst-obj)").unwrap();
        assert_eq!(x, 2.0);
        assert_eq!(y, 5.0);
        let dst_obj_2: TestObj = vm.get_clone("dst-obj").unwrap();
        assert_eq!(dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                        y: dst_obj.y + src_obj.y });
        let dst_obj_2: &TestObj = vm.get_ref("dst-obj").unwrap();
        assert_eq!(*dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                         y: dst_obj.y + src_obj.y });
        let dst_obj_2: &TestObj = vm.get_ref_mut("dst-obj").unwrap();
        assert_eq!(*dst_obj_2, TestObj { x: dst_obj.x + src_obj.x,
                                         y: dst_obj.y + src_obj.y });
    }
}
